/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition
import FailureOfComposition.NativeContextSpecialization.AuditFixtures
import Lean
import Lean.Compiler.NoncomputableAttr

/-!
Audit proof dependencies and the separation of the obstruction proof routes.
-/

open Lean Elab Command
open FailureOfComposition.ConcreteIndices
open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeEqualityTransport
open FailureOfComposition.NumericalDomainOrder
open FailureOfComposition.NumericalExtensionComposition
open FailureOfComposition.NumericalExtensionProofs
open FailureOfComposition.NumericalExtensionTheta
open FailureOfComposition.NumericalProductProofs
open FailureOfComposition.NumericalProofBridge
open FailureOfComposition.NumericalRangeProofs
open FailureOfComposition.PrfEqTransportRepair
open FailureOfComposition.TypedProgramCategory

/- An audit helper, not part of any mathematical proof. -/
private partial def collectDependencies (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: ns =>
    if seen.contains n then collectDependencies env ns seen
    else
      let seen := seen.insert n
      let more := match env.checked.get.find? n with
        | some (.axiomInfo v) => v.type.getUsedConstants
        | some (.defnInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
        | some (.thmInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
        | some (.opaqueInfo v) => v.type.getUsedConstants ++ v.value.getUsedConstants
        | some (.ctorInfo v) => v.type.getUsedConstants
        | some (.recInfo v) => v.type.getUsedConstants
        | some (.inductInfo v) => v.type.getUsedConstants ++ v.ctors.toArray
        | _ => #[]
      collectDependencies env (more.toList ++ ns) seen

/- The maintained project families.  Foundation, Mathlib, and Lean declarations
are library dependencies rather than declarations in these six roots. -/
private def nativeProjectRoots : Array Name := #[
  `Arith,
  `CategoricalRiceShapiro,
  `FailureOfComposition,
  `Metamath,
  `PCats,
  `RiceShapiro
]

private def nativeMPAllowedProjectNamespaces : Array Name := #[
  `Arith,
  `FailureOfComposition.NativeContextMP
]

private def nativeSubstitutionAllowedProjectNamespaces : Array Name := #[
  `FailureOfComposition.NativeSubstitution
]

private def nativeSpecializationAllowedProjectNamespaces : Array Name := #[
  `Arith.FixedFormulaNumeralSubstitution,
  `FailureOfComposition.NativeContextMP,
  `FailureOfComposition.NativeContextSpecialization,
  `FailureOfComposition.NativeSubstitution
]

private def nativeEqualityNumericalAllowedProjectNamespaces : Array Name := #[
  `Arith.FixedFormulaNumeralSubstitution,
  `CategoricalRiceShapiro.ArithmeticCode,
  `CategoricalRiceShapiro.Evaluator,
  `FailureOfComposition.NativeContextMP,
  `FailureOfComposition.NativeContextSpecialization,
  `FailureOfComposition.NativeEqualityTransport,
  `FailureOfComposition.NativeSubstitution
]

private def nativeEqualityInternalAllowedProjectNamespaces : Array Name := #[
  `Arith.FixedFormulaNumeralSubstitution,
  `CategoricalRiceShapiro.ArithmeticCode,
  `CategoricalRiceShapiro.Evaluator,
  `FailureOfComposition.NativeContextMP,
  `FailureOfComposition.NativeContextSpecialization,
  `FailureOfComposition.NativeEqualityTransport,
  `FailureOfComposition.NativeSubstitution
]

private def nativeEqualityBridgeAllowedProjectNamespaces : Array Name := #[
  `Arith.FixedFormulaNumeralSubstitution,
  `CategoricalRiceShapiro.ArithmeticCode,
  `CategoricalRiceShapiro.Evaluator,
  `FailureOfComposition.ConcreteEvaluator,
  `FailureOfComposition.NativeContextMP,
  `FailureOfComposition.NativeContextSpecialization,
  `FailureOfComposition.NativeEqualityTransport,
  `FailureOfComposition.NativeSubstitution,
  `FailureOfComposition.ProofSearch,
  `FailureOfComposition.UniformIndexQuotient
]

/- New allowances do not widen any earlier native inference boundary.  The
recognizer uses only numerical syntax and finite-set helpers; its equality
application additionally uses the existing equality syntax/transport.  The
eventual graph and quotient remain confined to the final theorem-only bridge. -/
private def nativeCheckerAllowedProjectNamespaces : Array Name := #[
  `Arith.FixedFormulaNumeralSubstitution,
  `FailureOfComposition.NativeContextMP,
  `FailureOfComposition.NativeContextSpecialization,
  `FailureOfComposition.NativeSubstitution,
  `FailureOfComposition.NativeSyntaxShift,
  `FailureOfComposition.NativeProofChecker
]

private def nativeEqCheckerAllowedProjectNamespaces : Array Name :=
  nativeCheckerAllowedProjectNamespaces ++ #[
    `CategoricalRiceShapiro.ArithmeticCode,
    `CategoricalRiceShapiro.Evaluator,
    `FailureOfComposition.NativeEqualityTransport
  ]

private def nativeCheckerBridgeAllowedProjectNamespaces : Array Name :=
  nativeEqCheckerAllowedProjectNamespaces ++ #[
    `FailureOfComposition.ConcreteEvaluator,
    `FailureOfComposition.ProofSearch,
    `FailureOfComposition.UniformIndexQuotient
  ]

/- Structural internal graphs use model-side choice to interpret functional
graphs.  This separate allowance preserves every earlier numerical boundary. -/
private def nativeInternalAllowedProjectNamespaces : Array Name :=
  nativeEqCheckerAllowedProjectNamespaces ++ #[
    `FailureOfComposition.NativeInternalSyntax,
    `FailureOfComposition.NativeInternalChecker,
    `FailureOfComposition.NativeInternalGraphs,
    `FailureOfComposition.NativeInternalCorrectness,
    `FailureOfComposition.NativeInternalSequence,
    `FailureOfComposition.NativeInternalNat,
    `FailureOfComposition.NativeInternalAxiomGraph,
    `FailureOfComposition.NativeInternalEquality,
    `FailureOfComposition.NativeInternalApplications
  ]

private def nativeInternalBridgeAllowedProjectNamespaces : Array Name :=
  nativeInternalAllowedProjectNamespaces ++ #[
    `FailureOfComposition.ConcreteEvaluator,
    `FailureOfComposition.ProofSearch,
    `FailureOfComposition.UniformIndexQuotient
  ]


/- Family extraction has its own allowances. No earlier boundary is widened.
Numerical bodies receive only the existing syntax/inference allowance. The
model-side layer adds fixed evaluator formulas; typed normalization remains
confined to the two named theorem-level dependencies below. -/
private def nativeFamilyNumericalAllowedProjectNamespaces : Array Name :=
  nativeEqualityNumericalAllowedProjectNamespaces ++ #[
    `FailureOfComposition.NativeFamilyExtraction,
    `FailureOfComposition.NativeFamilyConstructor,
    `FailureOfComposition.NativeFamilyPR,
    `FailureOfComposition.NativeFamilyNat,
    `FailureOfComposition.NativeFamilyNumeralInstances
  ]

private def nativeFamilyInternalAllowedProjectNamespaces : Array Name :=
  nativeInternalBridgeAllowedProjectNamespaces ++ #[
    `FailureOfComposition.NativeFamilyExtraction,
    `FailureOfComposition.NativeFamilyFormulas,
    `FailureOfComposition.NativeSigmaOneWitness,
    `FailureOfComposition.NativeFamilyConstructor,
    `FailureOfComposition.NativeFamilyPR,
    `FailureOfComposition.NativeFamilyNat,
    `FailureOfComposition.NativeFamilyInstances,
    `FailureOfComposition.NativeFamilySeed,
    `FailureOfComposition.NativeFamilyPreservation,
    `FailureOfComposition.NativeFamilyNumeralInstances,
    `FailureOfComposition.NativeFamilyApplications
  ]

/- The PA seed uses fixed-standard-index persistence/functionality. These
dependencies are not admitted to numerical or conditional inference roots. -/
private def nativeFamilyArithmeticAllowedProjectNamespaces : Array Name :=
  nativeFamilyInternalAllowedProjectNamespaces ++ #[
    `CategoricalRiceShapiro.PartialRecursive,
    `FailureOfComposition.ConcretePersistence,
    `FailureOfComposition.ConcreteWitnessGraphs,
    `FailureOfComposition.MinimizationPersistence
  ]

private def nativeFamilyTypedAllowedProjectNamespaces : Array Name :=
  nativeFamilyArithmeticAllowedProjectNamespaces ++ #[
    `FailureOfComposition.ProofSearchMembership.typedRepresentative,
    `FailureOfComposition.NativeFamilyTypedApplications,
    `FailureOfComposition.TypedProgramCategory,
    `FailureOfComposition.CodedObjectMembership,
    -- Existing normalization chooses a realizer; only this typed theorem's
    -- proof/type closure admits its compiler and semidecision dependencies.
    `FailureOfComposition.ArithmeticCodeCompiler,
    `FailureOfComposition.ArithmeticFormulaAtoms,
    `FailureOfComposition.ArithmeticProgramOperations,
    `FailureOfComposition.BoundedSemidecision,
    `FailureOfComposition.ConcreteConstructorGraphs,
    `FailureOfComposition.ConcreteEmptyGraph,
    `FailureOfComposition.ConcreteMinimizationGraph,
    `FailureOfComposition.ConcreteRecursionGraph,
    `FailureOfComposition.Kleene.identityIndex,
    `FailureOfComposition.ProgramGraph,
    `FailureOfComposition.SigmaOneGraphWitness,
    `FailureOfComposition.SigmaOneRealization,
    `FailureOfComposition.SigmaOneSearch,
    `FailureOfComposition.SigmaOneSemidecisionCore
  ]


/- Native membership assembly has separate allowances. Earlier arrays and
controls remain unchanged. Production membership is admitted only at the
single standard comparison root, never at an executable or internal root. -/
private def nativeMembershipNumericalAllowedProjectNamespaces : Array Name :=
  nativeFamilyNumericalAllowedProjectNamespaces ++ #[
    `FailureOfComposition.NativeMembershipAssembly,
    `FailureOfComposition.NativeMembershipConstructor,
    `FailureOfComposition.NativeMembershipPR
  ]

private def nativeMembershipInternalAllowedProjectNamespaces : Array Name :=
  nativeFamilyInternalAllowedProjectNamespaces ++ #[
    `FailureOfComposition.NativeMembershipAssembly,
    `FailureOfComposition.NativeMembershipFormulas,
    `FailureOfComposition.NativeMembershipConstructor,
    `FailureOfComposition.NativeMembershipPR,
    `FailureOfComposition.NativeMembershipInstances,
    `FailureOfComposition.NativeMembershipPreservation,
    `FailureOfComposition.NativeMembershipApplications
  ]

private def nativeMembershipArithmeticAllowedProjectNamespaces : Array Name :=
  nativeMembershipInternalAllowedProjectNamespaces ++ #[
    `CategoricalRiceShapiro.PartialRecursive,
    `FailureOfComposition.ConcretePersistence,
    `FailureOfComposition.ConcreteWitnessGraphs,
    `FailureOfComposition.MinimizationPersistence
  ]

private def nativeMembershipTypedAllowedProjectNamespaces : Array Name :=
  nativeMembershipArithmeticAllowedProjectNamespaces ++ nativeFamilyTypedAllowedProjectNamespaces ++ #[
    `FailureOfComposition.NativeMembershipTypedApplications
  ]

private def nativeMembershipProductionAllowedProjectNamespaces : Array Name :=
  nativeMembershipTypedAllowedProjectNamespaces ++ #[
    `FailureOfComposition.NativeMembershipProductionComparison,
    `Arith.Feferman.Structural,
    `Arith.Feferman.StructuralProof,
    `Arith.Feferman.Specialization,
    `Metamath.Feferman,
    `FailureOfComposition.NumericalProofBridge,
    `FailureOfComposition.NumericalSpecialization,
    `FailureOfComposition.GeneratedWitnessGraphs,
    `FailureOfComposition.FirstSuccessGraph,
    `FailureOfComposition.ProductiveDivergence,
    `FailureOfComposition.TheoryEnumerability,
    `FailureOfComposition.ProofSearchMembership,
    `FailureOfComposition.AxiomCodes,
    `FailureOfComposition.TheoremCodes,
    `FailureOfComposition.canonicalEvalnCode,
    `FailureOfComposition.canonicalPartrecGraphFormula,
    `FailureOfComposition.canonicalPartrecGraphFormula_eval_certificate_iff,
    `FailureOfComposition.canonicalPartrecGraphFormula_eval_iff,
    `FailureOfComposition.canonicalPartrecGraphFormula_eval_iff_eventualGraph,
    `FailureOfComposition.canonicalPartrecGraphFormula_eval_stage_bind_iff,
    `FailureOfComposition.firstSuccessGraph,
    `FailureOfComposition.firstSuccessGraph_eval,
    `FailureOfComposition.firstSuccessGraph_uniform_eventualGraph,
    `FailureOfComposition.firstSuccessGraph_val,
    `FailureOfComposition.firstSuccessfulEvalnStageCode,
    `FailureOfComposition.firstSuccessfulEvalnStageCode_eval_certificate_iff,
    `FailureOfComposition.firstSuccessfulEvalnStageCode_eval_iff,
    `FailureOfComposition.selectedStageSub_eval_certificate_iff,
    `FailureOfComposition.sentence_provability_re_of_delta1,
    `FailureOfComposition.theorem_codes_re_of_axiom_codes
  ]


/- Numeral arithmetic has separate syntax/inference-only allowances. Every
earlier array and private-owner control is preserved. No production, typed
normalization, chosen compiler, or program-quotient bridge is admitted here. -/
private def nativeNumeralNumericalAllowedProjectNamespaces : Array Name :=
  nativeSpecializationAllowedProjectNamespaces ++ #[
    `FailureOfComposition.NativeEqualityTransport,
    `FailureOfComposition.NativeFamilyExtraction,
    `FailureOfComposition.NativeFamilyConstructor,
    `FailureOfComposition.NativeFamilyPR,
    `FailureOfComposition.NativeFamilyNat,
    `FailureOfComposition.NativeFamilyNumeralInstances,
    `FailureOfComposition.NativeNumeralArithmetic,
    `FailureOfComposition.NativeNumeralSyntax,
    `FailureOfComposition.NativeNumeralSeeds,
    `FailureOfComposition.NativeNumeralSpecialization,
    `FailureOfComposition.NativeNumeralConstructor,
    `FailureOfComposition.NativeNumeralPR,
    `FailureOfComposition.NativeNumeralApplications
  ]

private def nativeNumeralInternalAllowedProjectNamespaces : Array Name :=
  nativeNumeralNumericalAllowedProjectNamespaces ++ nativeInternalAllowedProjectNamespaces ++ #[
    -- Stored preservation proofs also retain this earlier private PA-to-IΣ₁
    -- model helper. It is admitted only to full proof/type closures.
    `FailureOfComposition.NativeFamilyFormulas,
    `FailureOfComposition.NativeFamilyInstances,
    `FailureOfComposition.NativeFamilyPreservation,
    `FailureOfComposition.NativeSigmaOneWitness,
    `FailureOfComposition.NativeNumeralAdditionGraph,
    `FailureOfComposition.NativeNumeralMultiplicationGraph,
    `FailureOfComposition.NativeNumeralInstances,
    `FailureOfComposition.NativeNumeralPreservation,
    `FailureOfComposition.NativeNumeralProof
  ]

private def nativeProjectRoot? (name : Name) : Option Name :=
  nativeProjectRoots.find? fun root => root.isPrefixOf name

/- Recover the module encoded by Lean's private prefix.  This matches the
shape documented by `Lean.privatePrefix?`; it does not parse a rendered name. -/
private def privateOwnerModule? (name : Name) : Option Name :=
  match privatePrefix? name with
  | some (.num mangledModule 0) =>
      if privateHeader.isPrefixOf mangledModule then
        let owner := mangledModule.replacePrefix privateHeader .anonymous
        if owner == .anonymous then none else some owner
      else none
  | _ => none

private def declaringModule? (env : Environment) (name : Name) : Option Name :=
  match env.getModuleIdxFor? name with
  | some moduleIdx => env.header.moduleNames[moduleIdx.toNat]?
  | none => privateOwnerModule? name

/- Public declarations are classified by their user name.  A private
declaration from a project module is classified by that defining module, since
`privateToUserName` may recover only a short user name. -/
private def nativeClassificationName (env : Environment) (name : Name) : Name :=
  let userName := privateToUserName name
  if isPrivateName name then
    match declaringModule? env name with
    | some owner =>
        if (nativeProjectRoot? owner).isSome then owner else userName
    | none => userName
  else userName

private def isAllowedNativeProjectDependency (env : Environment)
    (allowedNamespaces : Array Name) (name : Name) : Bool :=
  let classificationName := nativeClassificationName env name
  match nativeProjectRoot? classificationName with
  | none => true
  | some _ => allowedNamespaces.any fun allowed =>
      allowed.isPrefixOf classificationName

private def hasForbiddenConsistencyBaseName (name : Name) : Bool :=
  let normalizedUserName := (privateToUserName name).toString
  normalizedUserName.endsWith "consistent_unprovable" ||
    normalizedUserName.endsWith "con_unprovable"

private def isForbiddenNativeDependency (env : Environment)
    (allowedNamespaces : Array Name) (name : Name) : Bool :=
  name == ``sorryAx ||
    hasForbiddenConsistencyBaseName name ||
    !isAllowedNativeProjectDependency env allowedNamespaces name

private def forbiddenNativeDependencies (env : Environment)
    (allowedNamespaces : Array Name) (root : Name) : Array Name :=
  (collectDependencies env [root]).toArray.filter fun name =>
    isForbiddenNativeDependency env allowedNamespaces name

private def directDefinitionDependencies (env : Environment) (root : Name) : Array Name :=
  match env.checked.get.find? root with
  | some (.defnInfo value) => value.value.getUsedConstants
  | some (.opaqueInfo value) => value.value.getUsedConstants
  | _ => #[]

private def directClassicalDependencies (env : Environment) (root : Name) : Array Name :=
  (directDefinitionDependencies env root).filter fun name =>
    `Classical |>.isPrefixOf (privateToUserName name)

/- Follow definition bodies, not theorem bodies or declaration types.  This
separate check looks for choice-based computational dependencies; the full
proof-and-type closure is still checked by forbiddenNativeDependencies. -/
private partial def collectDefinitionBodies (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | n :: ns =>
    if seen.contains n then collectDefinitionBodies env ns seen
    else
      let seen := seen.insert n
      let more := directDefinitionDependencies env n
      collectDefinitionBodies env (more.toList ++ ns) seen

private structure NumericalNativeAudit where
  taggedNoncomputable : Bool
  directClassical : Array Name
  forbidden : Array Name

private def numericalNativeAudit (env : Environment) (root : Name) : NumericalNativeAudit := {
  taggedNoncomputable := isNoncomputable env root
  directClassical := directClassicalDependencies env root
  forbidden := forbiddenNativeDependencies env nativeSpecializationAllowedProjectNamespaces root
}

/- Audit fixtures for the four namespace regressions.  Each wrapper has an
allowed-looking public name, so rejection must identify the dependency named
by the corresponding test. -/
private def nativeAuditPrivateForbiddenValue : Nat := 11

namespace FailureOfComposition.NativeDependencyAuditForbidden

/-- Public dependency outside every permitted native-specialization namespace. -/
def publicValue : Nat := 13

end FailureOfComposition.NativeDependencyAuditForbidden

namespace FailureOfComposition.NativeContextSpecializationExtra

/-- A dependency whose rendered name used to share an allowed textual prefix. -/
def publicValue : Nat := 17

end FailureOfComposition.NativeContextSpecializationExtra

namespace Metamath.NativeDependencyAuditForbidden

/-- A dependency in another maintained project family. -/
def publicValue : Nat := 19

end Metamath.NativeDependencyAuditForbidden

namespace FailureOfComposition.NativeContextSpecialization.DependencyAuditFixtures

/-- An allowed wrapper around a forbidden public project dependency. -/
def publicForbiddenWrapper : Nat :=
  FailureOfComposition.NativeDependencyAuditForbidden.publicValue

/-- An allowed wrapper around a forbidden private project dependency. -/
def privateForbiddenWrapper : Nat :=
  nativeAuditPrivateForbiddenValue

/-- An allowed wrapper around an allowed-looking namespace with an extra suffix. -/
def suffixForbiddenWrapper : Nat :=
  FailureOfComposition.NativeContextSpecializationExtra.publicValue

/-- An allowed wrapper around a dependency in the `Metamath` project family. -/
def otherFamilyForbiddenWrapper : Nat :=
  Metamath.NativeDependencyAuditForbidden.publicValue

/-- A longer public name ending in the first forbidden consistency suffix. -/
def auditLonger_consistent_unprovable : Nat := 23

/-- A longer public name ending in the second forbidden consistency suffix. -/
def auditLonger_con_unprovable : Nat := 29

def consistencySuffixForbiddenWrapper : Nat :=
  auditLonger_consistent_unprovable

def shortConsistencySuffixForbiddenWrapper : Nat :=
  auditLonger_con_unprovable

end FailureOfComposition.NativeContextSpecialization.DependencyAuditFixtures

open FailureOfComposition.NativeContextSpecialization.DependencyAuditFixtures

run_cmd do
  let env ← getEnv
  let cases : Array (String × Name × Name) := #[
    ("public forbidden project dependency",
      ``publicForbiddenWrapper,
      ``FailureOfComposition.NativeDependencyAuditForbidden.publicValue),
    ("private forbidden dependency through an allowed wrapper",
      ``privateForbiddenWrapper,
      ``nativeAuditPrivateForbiddenValue),
    ("allowed-looking namespace with an extra suffix",
      ``suffixForbiddenWrapper,
      ``FailureOfComposition.NativeContextSpecializationExtra.publicValue),
    ("dependency from the Metamath project family",
      ``otherFamilyForbiddenWrapper,
      ``Metamath.NativeDependencyAuditForbidden.publicValue),
    ("longer name ending in consistent_unprovable",
      ``consistencySuffixForbiddenWrapper,
      ``auditLonger_consistent_unprovable),
    ("longer name ending in con_unprovable",
      ``shortConsistencySuffixForbiddenWrapper,
      ``auditLonger_con_unprovable)
  ]
  for (label, root, expected) in cases do
    let actual := forbiddenNativeDependencies env
      nativeSpecializationAllowedProjectNamespaces root
    unless actual.contains expected do
      throwError "Native dependency regression '{label}' did not identify \
        {expected}; actual forbidden dependencies: {actual}"
    logInfo m!"Native dependency regression PASS ({label}): root {root}; \
      expected and identified dependency {expected}; all forbidden dependencies {actual}."
  let privateName := ``nativeAuditPrivateForbiddenValue
  let privateUserName := privateToUserName privateName
  let privateOwner := declaringModule? env privateName
  unless privateUserName == `nativeAuditPrivateForbiddenValue do
    throwError "Expected a short private user name, got {privateUserName} from {privateName}"
  unless privateOwner == some `FailureOfComposition.Verification.CheckDependencies do
    throwError "Expected the private fixture owner to be \
      FailureOfComposition.Verification.CheckDependencies, got {privateOwner}"
  unless nativeClassificationName env privateName ==
      `FailureOfComposition.Verification.CheckDependencies do
    throwError "Short private name was not classified by its defining project owner: \
      raw {privateName}; user {privateUserName}; owner {privateOwner}; \
      classification {nativeClassificationName env privateName}"
  logInfo m!"Native dependency regression PASS (short private user name): \
    raw {privateName}; user {privateUserName}; defining owner {privateOwner}; \
    classification {nativeClassificationName env privateName}."
  let noncomputableRoot :=
    ``FailureOfComposition.NativeContextSpecialization.AuditFixtures.noncomputableRoot
  let noncomputableAudit := numericalNativeAudit env noncomputableRoot
  let noncomputableDeps := collectDependencies env [noncomputableRoot]
  let allowedPrivateHelpers := noncomputableDeps.toArray.filter fun name =>
    isPrivateName name &&
      privateToUserName name ==
        `FailureOfComposition.NativeContextSpecialization.AuditFixtures.privateChoiceValue &&
      declaringModule? env name ==
        some `FailureOfComposition.NativeContextSpecialization.AuditFixtures
  unless allowedPrivateHelpers.size == 1 do
    throwError "Expected one private choice-producing fixture helper, got {allowedPrivateHelpers}"
  let privateChoiceHelper := allowedPrivateHelpers.getD 0 .anonymous
  unless isAllowedNativeProjectDependency env
      nativeSpecializationAllowedProjectNamespaces privateChoiceHelper do
    throwError "Legitimate allowed private helper was rejected: {privateChoiceHelper}; \
      owner {declaringModule? env privateChoiceHelper}; \
      classification {nativeClassificationName env privateChoiceHelper}"
  unless noncomputableAudit.taggedNoncomputable do
    throwError "Noncomputable numerical fixture root was not tagged: {noncomputableRoot}"
  unless noncomputableAudit.directClassical.isEmpty do
    throwError "Noncomputable fixture should reach choice only through its private helper; \
      direct Classical dependencies: {noncomputableAudit.directClassical}"
  unless noncomputableAudit.forbidden.isEmpty do
    throwError "The allowed private choice helper should not violate the project boundary: \
      {noncomputableAudit.forbidden}"
  unless noncomputableDeps.contains ``Classical.choice do
    throwError "Noncomputable fixture does not reach Classical.choice through {privateChoiceHelper}"
  logInfo m!"Native dependency regression PASS (noncomputable tag and allowed private \
    helper): root {noncomputableRoot}; private helper {privateChoiceHelper}; \
    user {privateToUserName privateChoiceHelper}; \
    owner {declaringModule? env privateChoiceHelper}; \
    classification {nativeClassificationName env privateChoiceHelper}; \
    tagged noncomputable; no direct Classical dependency; \
    transitive Classical.choice found."
  let negativeBodies := collectDefinitionBodies env [noncomputableRoot]
  unless negativeBodies.contains privateChoiceHelper &&
      negativeBodies.contains ``Classical.choice do
    throwError "Definition-body traversal missed the private-choice negative control"
  logInfo "Native definition-body regression PASS (private-choice negative control)."
  let positiveRoot :=
    ``FailureOfComposition.NativeContextSpecialization.AuditFixtures.theoremOnlyClassicalRoot
  let positiveFull := collectDependencies env [positiveRoot]
  let positiveBodies := collectDefinitionBodies env [positiveRoot]
  unless positiveFull.contains ``Classical.choice do
    throwError "The theorem-only classical control has no classical full dependency"
  if positiveBodies.contains ``Classical.choice || isNoncomputable env positiveRoot then
    throwError "Definition-body traversal followed a theorem proof in its positive control"
  logInfo "Native definition-body regression PASS (theorem-only classical positive control)."
  for root in [
      ``FailureOfComposition.NativeContextSpecialization.specializeCtx,
      ``FailureOfComposition.NativeContextSpecialization.specializeCtxPacked] do
    let audit := numericalNativeAudit env root
    if audit.taggedNoncomputable || !audit.directClassical.isEmpty || !audit.forbidden.isEmpty then
      throwError "Real numerical specialization root failed its positive regression: \
        {root}; tagged noncomputable {audit.taggedNoncomputable}; \
        direct Classical dependencies {audit.directClassical}; \
        forbidden dependencies {audit.forbidden}"
    let allowedPrivate := (collectDependencies env [root]).toArray.filter fun name =>
      isPrivateName name &&
        (nativeProjectRoot? (nativeClassificationName env name)).isSome &&
        isAllowedNativeProjectDependency env
          nativeSpecializationAllowedProjectNamespaces name
    unless !allowedPrivate.isEmpty do
      throwError "Real numerical specialization root has no accepted private helper control: {root}"
    logInfo m!"Native dependency regression PASS (real computable specialization root): \
      {root}; accepted private helpers {allowedPrivate}; classical theorem proofs remain \
      outside this numerical-body check."

run_cmd do
  let env ← getEnv
  for root in [``Arith.Feferman.Specialization.provable_PA_uniformSpecializationPreservation,
      ``Arith.Feferman.Specialization.provable_PA_uniformForwardTransferPreservation,
      ``Arith.Feferman.Specialization.provable_PA_uniformReverseTransferPreservation,
      ``FailureOfComposition.NumericalSpecialization.PA_provable_iff_exists_stage_proof_T,
      ``FailureOfComposition.NumericalSpecialization.proof_T_specialize_firstSuccess_eventual,
      ``FailureOfComposition.NumericalSpecialization.proof_T_transfer_firstSuccess_to_eventual,
      ``FailureOfComposition.NumericalSpecialization.proof_T_transfer_eventual_to_firstSuccess,
      ``FailureOfComposition.NumericalSpecialization.transfer_firstSuccess_to_eventual_sound,
      ``FailureOfComposition.NumericalSpecialization.transfer_eventual_to_firstSuccess_sound,
      ``FailureOfComposition.NumericalProofBridge.paExtendedProofGraph_nat_iff,
      ``FailureOfComposition.NumericalProofBridge.provable_PA_paEqualityBridgePreservation,
      ``FailureOfComposition.NumericalProofBridge.provable_PA_paLeftBridgePreservation,
      ``FailureOfComposition.NumericalProofBridge.provable_PA_paRightBridgePreservation,
      ``PA_provable_uniform_iff_exists_equalityCode_proof_T,
      ``PA_provable_left_iff_exists_leftInstanceCode_proof_T,
      ``PA_provable_right_iff_exists_rightInstanceCode_proof_T,
      ``FailureOfComposition.NumericalProofBridge.provable_PA_paForwardFromStagesPreservation,
      ``FailureOfComposition.NumericalProofBridge.provable_PA_paReverseFromStagesPreservation,
      ``FailureOfComposition.NumericalProofBridge.identity_zero_bridge_transfer_application,
      ``FailureOfComposition.NumericalProofBridge.identity_zero_bridge_transfer_sound,
      ``FailureOfComposition.NumericalProofBridge.reTheoryExtendedProofGraph_nat_iff,
      ``FailureOfComposition.NumericalProofBridge.extendedProof_T_meaning_sound_in,
      ``FailureOfComposition.NumericalProofBridge.reTheory_provable_iff_exists_stage_proof_T,
      ``reTheory_provable_uniform_iff_exists_equalityCode_proof_T,
      ``reTheory_provable_left_iff_exists_leftInstanceCode_proof_T,
      ``reTheory_provable_right_iff_exists_rightInstanceCode_proof_T,
      ``FailureOfComposition.NumericalProofBridge.reTheory_transferForwardFromStages_sound,
      ``FailureOfComposition.NumericalProofBridge.reTheory_transferReverseFromStages_sound,
      ``FailureOfComposition.NumericalProofBridge.provable_PA_reTheoryEqualityBridgePreservation,
      ``FailureOfComposition.NumericalProofBridge.provable_PA_reTheoryLeftBridgePreservation,
      ``FailureOfComposition.NumericalProofBridge.provable_PA_reTheoryRightBridgePreservation,
      ``FailureOfComposition.NumericalProofBridge.provable_PA_reTheoryForwardFromStagesPreservation,
      ``FailureOfComposition.NumericalProofBridge.provable_PA_reTheoryReverseFromStagesPreservation,
      ``paSingletonExtension_added_axiom_has_stage_proof] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n => n.toString == "sorryAx"
    unless forbidden.isEmpty do
      throwError "Forbidden numerical-specialization dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected numerical-specialization axioms: {unexpected}"
    logInfo m!"Numerical specialization result {root}: {deps.size} declarations; \
      no sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``Arith.FixedFormulaNumeralSubstitution.formulaNegCode_encode,
      ``FailureOfComposition.NativeContextMP.primrec_mpCtxPacked,
      ``FailureOfComposition.NativeContextMP.mpCtxGraph_nat_iff,
      ``FailureOfComposition.NativeContextMP.mpCtxGraph_total,
      ``FailureOfComposition.NativeContextMP.mpCtxGraph_functional,
      ``FailureOfComposition.NativeContextMP.derivationOf_mpCtxValue,
      ``FailureOfComposition.NativeContextMP.mpCtxGraph_preserves_derivationOf,
      ``FailureOfComposition.NativeContextMP.proof_mpCtx,
      ``FailureOfComposition.NativeContextMP.derivationOf_mpCtx_singleton,
      ``FailureOfComposition.NativeContextMP.craig_mpCtxGraph_preserves_derivationOf,
      ``FailureOfComposition.NativeContextMP.craig_provable_iff] do
    let deps := collectDependencies env [root]
    let forbidden := forbiddenNativeDependencies env
      nativeMPAllowedProjectNamespaces root
    unless forbidden.isEmpty do
      throwError "Forbidden native-context-MP dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected native-context-MP axioms: {unexpected}"
    logInfo m!"Native-context MP result {root}: {deps.size} declarations; \
      Foundation/Arith only, with no project checker, consistency, or sorryAx \
      dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.NativeSubstitution.primrecPred_termCodeValid,
      ``FailureOfComposition.NativeSubstitution.primrecPred_formulaBodyCodeValid,
      ``FailureOfComposition.NativeSubstitution.primrec₂_subst1Code,
      ``FailureOfComposition.NativeSubstitution.subst1Code_encode,
      ``FailureOfComposition.NativeSubstitution.subst1Code_eq_substs1,
      ``FailureOfComposition.NativeSubstitution.subst1Graph_nat_iff,
      ``FailureOfComposition.NativeSubstitution.subst1Graph_total,
      ``FailureOfComposition.NativeSubstitution.subst1Graph_functional,
      ``FailureOfComposition.NativeSubstitution.subst1Value_eq_substs1,
      ``FailureOfComposition.NativeSubstitution.subst1Value_isSemiformula,
      ``FailureOfComposition.NativeSubstitution.subst1Value_neg,
      ``FailureOfComposition.NativeSubstitution.freeVariable_code,
      ``FailureOfComposition.NativeSubstitution.nestedQuantifier_code] do
    let deps := collectDependencies env [root]
    let forbidden := forbiddenNativeDependencies env
      nativeSubstitutionAllowedProjectNamespaces root
    unless forbidden.isEmpty do
      throwError "Forbidden native-substitution dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected native-substitution axioms: {unexpected}"
    logInfo m!"Native substitution result {root}: {deps.size} declarations; \
      Foundation only, with no project proof checker, consistency, or sorryAx \
      dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.NativeContextSpecialization.specializeCtx,
      ``FailureOfComposition.NativeContextSpecialization.specializeCtxPacked] do
    let deps := collectDependencies env [root]
    let audit := numericalNativeAudit env root
    if audit.taggedNoncomputable then
      throwError "Noncomputable numerical native-specialization root: {root}"
    unless audit.directClassical.isEmpty do
      throwError "Classical constant in numerical native-specialization body: \
        {audit.directClassical}"
    unless audit.forbidden.isEmpty do
      throwError "Forbidden numerical native-specialization dependencies: {audit.forbidden}"
    logInfo m!"Numerical native-specialization definition {root}: root is not \
      tagged noncomputable; no Classical constant occurs directly in its executable \
      body; its {deps.size}-declaration transitive closure has no dependency outside \
      the four permitted project namespaces and no consistency or sorryAx dependency."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.NativeContextSpecialization.primrec_specializeCtxPacked,
      ``FailureOfComposition.NativeContextSpecialization.specializeCtxGraph_iff,
      ``FailureOfComposition.NativeContextSpecialization.specializeCtxGraph_total,
      ``FailureOfComposition.NativeContextSpecialization.specializeCtxGraph_functional,
      ``FailureOfComposition.NativeContextSpecialization.derivationOf_specializeCtxValue,
      ``FailureOfComposition.NativeContextSpecialization.specializeCtxGraph_preserves_derivationOf,
      ``specializeCtxGraph_preserves_derivationOf_arith,
      ``FailureOfComposition.NativeContextSpecialization.specializeCtxValue_nat,
      ``FailureOfComposition.NativeContextSpecialization.specializeCtxGraph_nat_iff,
      ``FailureOfComposition.NativeContextSpecialization.derivationOf_specializeCtx,
      ``FailureOfComposition.NativeContextSpecialization.proof_specializeCtxValue,
      ``FailureOfComposition.NativeContextSpecialization.proof_specializeCtx,
      ``FailureOfComposition.NativeContextSpecialization.derivationOf_specializeCtxValue_singleton,
      ``FailureOfComposition.NativeContextSpecialization.derivationOf_specializeCtx_singleton,
      ``craig_specializeCtxGraph_preserves_derivationOf,
      ``FailureOfComposition.NativeContextSpecialization.craig_proof_specializeCtx,
      ``FailureOfComposition.NativeContextSpecialization.craig_provable_iff] do
    let deps := collectDependencies env [root]
    let forbidden := forbiddenNativeDependencies env
      nativeSpecializationAllowedProjectNamespaces root
    unless forbidden.isEmpty do
      throwError "Forbidden native-context-specialization dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected native-context-specialization axioms: {unexpected}"
    logInfo m!"Native context-specialization result {root}: {deps.size} declarations; \
      only the specialization, substitution, context-MP, and fixed-negation project \
      namespaces are permitted; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.NativeEqualityTransport.numeralTermCode,
      ``FailureOfComposition.NativeEqualityTransport.nativeEqCode,
      ``FailureOfComposition.NativeEqualityTransport.thetaCode,
      ``FailureOfComposition.NativeEqualityTransport.secondBodyCode,
      ``FailureOfComposition.NativeEqualityTransport.thirdBodyCode,
      ``FailureOfComposition.NativeEqualityTransport.implicationCode,
      ``FailureOfComposition.NativeEqualityTransport.transportCtxWithSeed,
      ``FailureOfComposition.NativeEqualityTransport.transportCtxWithSeedPacked,
      ``FailureOfComposition.NativeEqualityTransport.transportCtxForSeed,
      ``FailureOfComposition.NativeEqualityTransport.transportCtxForSeedPacked] do
    let deps := collectDependencies env [root]
    let taggedNoncomputable := isNoncomputable env root
    let directClassical := directClassicalDependencies env root
    let forbidden := forbiddenNativeDependencies env
      nativeEqualityNumericalAllowedProjectNamespaces root
    if taggedNoncomputable then
      throwError "Noncomputable numerical native-equality root: {root}"
    unless directClassical.isEmpty do
      throwError "Classical constant in numerical native-equality body: \
        {directClassical}"
    unless forbidden.isEmpty do
      throwError "Forbidden numerical native-equality dependencies: {forbidden}"
    logInfo m!"Numerical native-equality definition {root}: {deps.size} declarations; \
      computable body using only the fixed syntax/evaluator and native inference \
      namespaces; no production/repaired checker, consistency, or sorryAx dependency."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.NativeEqualityTransport.primrec₂_nativeEqCode,
      ``FailureOfComposition.NativeEqualityTransport.primrec_transportCtxWithSeedPacked,
      ``FailureOfComposition.NativeEqualityTransport.eqValueGraph_iff,
      ``FailureOfComposition.NativeEqualityTransport.eqValueGraph_total,
      ``FailureOfComposition.NativeEqualityTransport.eqValueGraph_functional,
      ``FailureOfComposition.NativeEqualityTransport.eqValue_nat,
      ``FailureOfComposition.NativeEqualityTransport.eqValueGraph_nat_iff,
      ``FailureOfComposition.NativeEqualityTransport.eqValue_isFormula,
      ``FailureOfComposition.NativeEqualityTransport.numeralTermCodeGraph_iff,
      ``FailureOfComposition.NativeEqualityTransport.numeralTermCodeGraph_total,
      ``FailureOfComposition.NativeEqualityTransport.numeralTermCodeGraph_functional,
      ``FailureOfComposition.NativeEqualityTransport.numeralTermCodeValue_nat,
      ``FailureOfComposition.NativeEqualityTransport.numeralTermCodeGraph_nat_iff,
      ``FailureOfComposition.NativeEqualityTransport.thetaBodyQ_substs_internal,
      ``FailureOfComposition.NativeEqualityTransport.secondBody_substs_internal,
      ``FailureOfComposition.NativeEqualityTransport.thirdBody_substs_internal,
      ``FailureOfComposition.NativeEqualityTransport.transportGraph_iff,
      ``FailureOfComposition.NativeEqualityTransport.transportGraph_total,
      ``FailureOfComposition.NativeEqualityTransport.transportGraph_functional,
      ``FailureOfComposition.NativeEqualityTransport.transportGraph_nat_iff,
      ``FailureOfComposition.NativeEqualityTransport.derivationOf_transportValue,
      ``FailureOfComposition.NativeEqualityTransport.transportGraph_preserves_derivationOf,
      ``FailureOfComposition.NativeEqualityTransport.primrec_transportCtxForSeedPacked,
      ``FailureOfComposition.NativeEqualityTransport.derivationOf_transportCtxWithSeed] do
    let deps := collectDependencies env [root]
    let forbidden := forbiddenNativeDependencies env
      nativeEqualityInternalAllowedProjectNamespaces root
    unless forbidden.isEmpty do
      throwError "Forbidden internal native-equality dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected internal native-equality axioms: {unexpected}"
    logInfo m!"Internal native-equality result {root}: {deps.size} declarations; \
      only fixed syntax/evaluator and native inference namespaces; no \
      production/repaired checker, consistency, or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.NativeEqualityTransport.equalityFormula_instance,
      ``FailureOfComposition.NativeEqualityTransport.exists_uniform_theta_seed,
      ``FailureOfComposition.NativeEqualityTransport.exists_uniform_native_transport,
      ``FailureOfComposition.NativeEqualityTransport.proof_transportWithSeed,
      ``FailureOfComposition.NativeEqualityTransport.derivationOf_transportCtxWithSeed_singleton,
      ``FailureOfComposition.NativeEqualityTransport.craig_transportGraph_preserves_derivationOf,
      ``FailureOfComposition.NativeEqualityTransport.craig_proof_transportWithSeed,
      ``FailureOfComposition.NativeEqualityTransport.craig_proof_nativeEqCode_iff_eqIndex] do
    let deps := collectDependencies env [root]
    let forbidden := forbiddenNativeDependencies env
      nativeEqualityBridgeAllowedProjectNamespaces root
    unless forbidden.isEmpty do
      throwError "Forbidden theorem-only native-equality dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected theorem-only native-equality axioms: {unexpected}"
    logInfo m!"Theorem-only native-equality bridge {root}: {deps.size} declarations; \
      the eventual graph/uniform quotient namespaces are admitted only here; no \
      production/repaired checker, consistency, or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  let syntaxRoots := [
    ``FailureOfComposition.NativeSyntaxShift.termShiftRaw,
    ``FailureOfComposition.NativeSyntaxShift.formulaShiftRaw,
    ``FailureOfComposition.NativeSyntaxShift.termShiftCode,
    ``FailureOfComposition.NativeSyntaxShift.formulaShiftCode,
    ``FailureOfComposition.NativeSyntaxShift.formulaFreeCode,
    ``FailureOfComposition.NativeSyntaxShift.formulaSetCodeValid,
    ``FailureOfComposition.NativeSyntaxShift.sequentShiftCode,
    ``FailureOfComposition.NativeProofChecker.conclusionCode,
    ``FailureOfComposition.NativeProofChecker.sequentMemCode,
    ``FailureOfComposition.NativeProofChecker.sequentSubsetCode,
    ``FailureOfComposition.NativeProofChecker.ruleBodyCheck,
    ``FailureOfComposition.NativeProofChecker.ruleCheck,
    ``FailureOfComposition.NativeProofChecker.checkTable,
    ``FailureOfComposition.NativeProofChecker.nativeDerivationCheck,
    ``FailureOfComposition.NativeProofChecker.nativeDerivationOfCheck,
    ``FailureOfComposition.NativeProofChecker.nativeProofCheck]
  let equalityRoots := [
    ``FailureOfComposition.NativeProofChecker.nativeEqProofCheck,
    ``FailureOfComposition.NativeProofChecker.nativeEqProofCheckPacked,
    ``FailureOfComposition.NativeProofChecker.proofTransportPacked]
  for root in syntaxRoots ++ equalityRoots do
    let allowed := if syntaxRoots.contains root then
      nativeCheckerAllowedProjectNamespaces else nativeEqCheckerAllowedProjectNamespaces
    let deps := collectDependencies env [root]
    let forbidden := forbiddenNativeDependencies env allowed root
    if isNoncomputable env root then
      throwError "Noncomputable native-checker definition: {root}"
    unless (directClassicalDependencies env root).isEmpty do
      throwError "Classical constant directly in native-checker body: {root}"
    let computational := collectDefinitionBodies env [root]
    let choiceBased := computational.toArray.filter fun n =>
      (`Classical).isPrefixOf (privateToUserName n)
    unless choiceBased.isEmpty do
      throwError "Choice-based native-checker definition dependency: {choiceBased}"
    unless forbidden.isEmpty do
      throwError "Forbidden native-checker dependencies: {forbidden}"
    logInfo m!"Executable native-checker root {root}: {deps.size} declarations; \
      {computational.size} definition-body dependencies; no noncomputable tag, \
      Classical computational dependency, production/repaired checker, consistency, or sorryAx."

run_cmd do
  let env ← getEnv
  let recognitionRoots := [
    ``FailureOfComposition.NativeSyntaxShift.primrec_termShiftCode,
    ``FailureOfComposition.NativeSyntaxShift.primrec_formulaShiftCode,
    ``FailureOfComposition.NativeSyntaxShift.primrec_formulaFreeCode,
    ``FailureOfComposition.NativeSyntaxShift.primrec_sequentShiftCode,
    ``FailureOfComposition.NativeSyntaxShift.termShiftCode_eq_termShift,
    ``FailureOfComposition.NativeSyntaxShift.formulaShiftCode_eq_shift,
    ``FailureOfComposition.NativeSyntaxShift.formulaFreeCode_eq_free,
    ``FailureOfComposition.NativeSyntaxShift.sequentShiftCode_eq_setShift,
    ``FailureOfComposition.NativeProofChecker.primrec_nativeDerivationCheck,
    ``FailureOfComposition.NativeProofChecker.primrec₂_nativeDerivationOfCheck,
    ``FailureOfComposition.NativeProofChecker.primrec₂_nativeProofCheck,
    ``FailureOfComposition.NativeProofChecker.nativeDerivationCheck_iff,
    ``FailureOfComposition.NativeProofChecker.nativeDerivationOfCheck_iff,
    ``FailureOfComposition.NativeProofChecker.nativeProofCheck_iff,
    ``FailureOfComposition.NativeProofChecker.primrecPred_derivationOf,
    ``FailureOfComposition.NativeProofChecker.primrecPred_proof,
    ``FailureOfComposition.NativeProofChecker.craig_codes_iff_deltaOneClass,
    ``FailureOfComposition.NativeProofChecker.exists_craig_axiomTest,
    ``FailureOfComposition.NativeProofChecker.primrecPred_craig_derivationOf,
    ``FailureOfComposition.NativeProofChecker.primrecPred_craig_proof]
  let equalityRoots := [
    ``FailureOfComposition.NativeProofChecker.primrec_nativeEqProofCheckPacked,
    ``FailureOfComposition.NativeProofChecker.nativeEqProofCheck_iff,
    ``FailureOfComposition.NativeProofChecker.primrec_proofTransportPacked]
  let bridge := ``FailureOfComposition.NativeProofChecker.exists_craig_nativeEq_checker_transport
  for root in recognitionRoots ++ equalityRoots ++ [bridge] do
    let allowed := if root == bridge then nativeCheckerBridgeAllowedProjectNamespaces
      else if equalityRoots.contains root then nativeEqCheckerAllowedProjectNamespaces
      else nativeCheckerAllowedProjectNamespaces
    let deps := collectDependencies env [root]
    let forbidden := forbiddenNativeDependencies env allowed root
    unless forbidden.isEmpty do
      throwError "Forbidden native-checker theorem dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected native-checker axioms: {unexpected}"
    logInfo m!"Native-checker theorem {root}: {deps.size} declarations; separate \
      recognition/equality/theorem-only bridge allowances; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.UniformIndexQuotient.eqIndex_comp_congr,
      ``FailureOfComposition.UniformIndexQuotient.eqIndex_comp_assoc,
      ``FailureOfComposition.UniformIndexQuotient.eqIndex_identity_comp,
      ``FailureOfComposition.UniformIndexQuotient.eqIndex_comp_identity,
      ``FailureOfComposition.UniformIndexQuotient.classOf_eq_classOf_iff,
      ``FailureOfComposition.UniformIndexQuotient.one_mul_classOf,
      ``FailureOfComposition.UniformIndexQuotient.classOf_mul_one,
      ``FailureOfComposition.UniformIndexQuotient.primrecPred_prfEq,
      ``FailureOfComposition.UniformIndexQuotient.classOf_eq_classOf_iff_exists_prfEq,
      ``FailureOfComposition.UniformIndexQuotient.eqIndex_provable_instance_iff,
      ``FailureOfComposition.UniformIndexQuotient.provableAt_classOf_iff_exists_rightProof,
      ``FailureOfComposition.UniformIndexQuotient.provableAt_classOf_iff_exists_leftProof,
      ``FailureOfComposition.UniformIndexQuotient.provableAt_one,
      ``FailureOfComposition.UniformIndexQuotient.exists_identity_rightProof] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex
    unless forbidden.isEmpty do
      throwError "Forbidden uniform-index-quotient dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected uniform-index-quotient axioms: {unexpected}"
    logInfo m!"Uniform index quotient result {root}: {deps.size} declarations; \
      no pointwise/generated quotient, Godel-II, or sorryAx dependency; \
      axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.CodedObjectMembership.primrec_member,
      ``FailureOfComposition.CodedObjectMembership.primrecPred_member,
      ``FailureOfComposition.CodedObjectMembership.natPairFormula_nat_iff,
      ``FailureOfComposition.CodedObjectMembership.natPairFormula_existsUnique_inputs,
      ``FailureOfComposition.CodedObjectMembership.memberFormula_numeral_iff,
      ``FailureOfComposition.CodedObjectMembership.memberFormula_nat_iff,
      ``FailureOfComposition.CodedObjectMembership.pa_proves_memberProductLaw,
      ``FailureOfComposition.CodedObjectMembership.pa_proves_memberCoproductLaw,
      ``FailureOfComposition.CodedObjectMembership.pa_proves_memberProductPairLaw,
      ``FailureOfComposition.CodedObjectMembership.pa_proves_memberCoproductLeftLaw,
      ``FailureOfComposition.CodedObjectMembership.pa_proves_memberCoproductRightLaw,
      ``FailureOfComposition.CodedObjectMembership.pa_proves_memberCoproductInvalidTagLaw,
      ``FailureOfComposition.CodedObjectMembership.pa_proves_member_of_true,
      ``FailureOfComposition.CodedObjectMembership.pa_proves_not_member_of_false,
      ``FailureOfComposition.CodedObjectMembership.pa_proves_nestedExample_left,
      ``FailureOfComposition.CodedObjectMembership.pa_proves_nestedExample_right,
      ``FailureOfComposition.CodedObjectMembership.pa_proves_not_nestedExample_invalid_tag] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n == ``Metamath.Feferman.codePair ||
      n == ``Arith.Feferman.Structural.codePairGraph ||
      n == ``FailureOfComposition.UniformIndexQuotient.EqIndex ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel
    unless forbidden.isEmpty do
      throwError "Forbidden coded-object-membership dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected coded-object-membership axioms: {unexpected}"
    logInfo m!"Coded object membership result {root}: {deps.size} declarations; \
      no bit-interleaving pair, quotient relation, or sorryAx dependency; \
      axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.TypedProgramCategory.deltaIndex_uniform,
      ``FailureOfComposition.TypedProgramCategory.eventualGraph_deltaIndex_eval,
      ``FailureOfComposition.TypedProgramCategory.deltaIndex_comp_self_in,
      ``FailureOfComposition.TypedProgramCategory.normalizeIndex_uniform,
      ``FailureOfComposition.TypedProgramCategory.primrec_normalizeIndex,
      ``FailureOfComposition.TypedProgramCategory.normalizeIndex_idempotent,
      ``FailureOfComposition.TypedProgramCategory.proves_support_iff_eqIndex_normalize,
      ``FailureOfComposition.TypedProgramCategory.eqIndex_restrict_iff_proves_sourceEquality,
      ``eqIndex_normalize_restrict_iff_proves_targetPreservation,
      ``FailureOfComposition.TypedProgramCategory.pa_proves_normalized_support,
      ``FailureOfComposition.TypedProgramCategory.objectIdempotent_mul_self,
      ``FailureOfComposition.TypedProgramCategory.objectIdempotent_omega,
      ``FailureOfComposition.TypedProgramCategory.arrowOfIndex_val,
      ``FailureOfComposition.TypedProgramCategory.exists_arrowOfIndex,
      ``FailureOfComposition.TypedProgramCategory.arrowOfIndex_eq_iff_eqIndex_normalize,
      ``FailureOfComposition.TypedProgramCategory.arrowOfIndex_comp,
      ``FailureOfComposition.TypedProgramCategory.omegaEndEquiv_id,
      ``FailureOfComposition.TypedProgramCategory.omegaEndEquiv_comp,
      ``FailureOfComposition.TypedProgramCategory.arrowOfIndex_eq_iff_exists_prfEq,
      ``FailureOfComposition.TypedProgramCategory.primrecPred_arrowPrfEq,
      ``FailureOfComposition.TypedProgramCategory.identityArrow_provableAt_of_member,
      ``FailureOfComposition.TypedProgramCategory.exists_identityArrow_rightProof_of_member,
      ``FailureOfComposition.TypedProgramCategory.proves_not_coproductIdentity_invalidTag] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex ||
      n == ``FailureOfComposition.UnaryPartrec
    unless forbidden.isEmpty do
      throwError "Forbidden typed-program-category dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected typed-program-category axioms: {unexpected}"
    logInfo m!"Typed program category result {root}: {deps.size} declarations; \
      no pointwise/generated quotient, extensional-function quotient, consistency, \
      or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.TypedNearProduct.primrec₂_tensorIndex,
      ``FailureOfComposition.TypedNearProduct.tensorIndex_uniform,
      ``FailureOfComposition.TypedNearProduct.codedProgramCategoryPCategory,
      ``FailureOfComposition.TypedNearProduct.domainArrow_eq_rst,
      ``FailureOfComposition.TypedNearProduct.arrowOfIndex_isTotal_iff_proves_typedTotality,
      ``FailureOfComposition.TypedNearProduct.nestedProduct_firstProjection_isTotal] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex ||
      n == ``FailureOfComposition.UnaryPartrec ||
      n == ``FailureOfComposition.TypedProgramCategory.ArrowPrfEq ||
      n == ``FailureOfComposition.UniformIndexQuotient.PrfEq ||
      n == ``CategoryTheory.RestrictionCategory.Split
    unless forbidden.isEmpty do
      throwError "Forbidden typed-near-product dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected typed-near-product axioms: {unexpected}"
    logInfo m!"Typed near-product result {root}: {deps.size} declarations; \
      no pointwise/generated quotient, numerical proof presentation, split \
      restriction, consistency, or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.TypedRanges.typedRangeIndex_normalized_uniform,
      ``FailureOfComposition.TypedRanges.eqIndex_range_congr,
      ``FailureOfComposition.TypedRanges.rangeArrow_arrowOfIndex,
      ``FailureOfComposition.TypedRanges.typedRangeIndex_normalize_eq,
      ``FailureOfComposition.TypedRanges.rangeArrow_eq_arrowOfIndex_of_realizes,
      ``FailureOfComposition.TypedRanges.rangeArrow_isRange,
      ``FailureOfComposition.TypedRanges.codedProgramCategoryHasRanges,
      ``FailureOfComposition.TypedRanges.ran_nearProd_map,
      ``FailureOfComposition.TypedRanges.codedProgramCategoryIsRP,
      ``FailureOfComposition.TypedRanges.ran_firstProjection_product_omega,
      ``FailureOfComposition.TypedRanges.typedRangeIndex_provable_iff] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex ||
      n == ``FailureOfComposition.UnaryPartrec ||
      n == ``FailureOfComposition.TypedProgramCategory.ArrowPrfEq ||
      n == ``FailureOfComposition.UniformIndexQuotient.PrfEq ||
      n == ``CategoryTheory.RestrictionCategory.Split
    unless forbidden.isEmpty do
      throwError "Forbidden typed-range dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected typed-range axioms: {unexpected}"
    logInfo m!"Typed range result {root}: {deps.size} declarations; \
      no pointwise/generated quotient, numerical proof presentation, split \
      restriction, consistency, or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.UniformRange.primrec_uniformRangeIndex,
      ``FailureOfComposition.UniformRange.eventualGraph_uniformRangeIndex_eval,
      ``FailureOfComposition.UniformRange.uniformRangeIndex_realizes,
      ``FailureOfComposition.UniformRange.uniformRangeIndex_eval,
      ``FailureOfComposition.UniformRange.eqIndex_uniformRangeIndex_rangeIndex,
      ``FailureOfComposition.UniformRange.eqIndex_uniformRangeIndex_congr,
      ``FailureOfComposition.UniformRange.primrec_typedUniformRangeIndex,
      ``FailureOfComposition.UniformRange.eventualGraph_typedUniformRangeIndex_normalized_eval,
      ``FailureOfComposition.UniformRange.pa_proves_typedUniformRangeIndex_support,
      ``FailureOfComposition.UniformRange.eqIndex_typedUniformRangeIndex_typedRangeIndex,
      ``FailureOfComposition.UniformRange.eqIndex_typedUniformRangeIndex_congr,
      ``FailureOfComposition.UniformRange.ran_arrowOfIndex_eq_uniformRange] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex ||
      n == ``FailureOfComposition.UnaryPartrec ||
      n == ``FailureOfComposition.TypedProgramCategory.ArrowPrfEq ||
      n == ``FailureOfComposition.UniformIndexQuotient.PrfEq ||
      n == ``CategoryTheory.RestrictionCategory.Split ||
      n.toString.startsWith
        "FailureOfComposition.NumericalRangeProofs" ||
      n.toString.startsWith
        "FailureOfComposition.ProofSearchMembership" ||
      n.toString.startsWith
        "FailureOfComposition.PrfEqTransportRepair" ||
      n.toString.startsWith
        "FailureOfComposition.NumericalExtensionComposition" ||
      n.toString.startsWith
        "FailureOfComposition.NumericalExtensionTheta"
    unless forbidden.isEmpty do
      throwError "Forbidden uniform-range dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected uniform-range axioms: {unexpected}"
    logInfo m!"Uniform range result {root}: {deps.size} declarations; \
      no numerical proof presentation, production proof-search boundary, additive \
      repair, pointwise/generated quotient, consistency, or sorryAx dependency; \
      axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.TypedCoproducts.typedCoprodIndex_uniform,
      ``FailureOfComposition.TypedCoproducts.eqIndex_coprod_congr,
      ``FailureOfComposition.TypedCoproducts.typedCoprodMap_arrowOfIndex,
      ``FailureOfComposition.TypedCoproducts.codedProgramCategoryHasCoproducts,
      ``FailureOfComposition.TypedCoproducts.typed_existsUnique_copair,
      ``FailureOfComposition.TypedCoproducts.typed_i0_isTotal,
      ``FailureOfComposition.TypedCoproducts.typed_i1_isTotal,
      ``FailureOfComposition.TypedCoproducts.distribLeftIndex_uniform,
      ``FailureOfComposition.TypedCoproducts.distribRightIndex_uniform,
      ``FailureOfComposition.TypedCoproducts.distribLeftInvIndex_uniform,
      ``FailureOfComposition.TypedCoproducts.distribRightInvIndex_uniform,
      ``FailureOfComposition.TypedCoproducts.distribLeft_eq_arrowOfIndex,
      ``FailureOfComposition.TypedCoproducts.distribRight_eq_arrowOfIndex,
      ``FailureOfComposition.TypedCoproducts.typed_distribLeft_hom_inv,
      ``FailureOfComposition.TypedCoproducts.typed_distribLeft_inv_hom,
      ``FailureOfComposition.TypedCoproducts.typed_distribRight_hom_inv,
      ``FailureOfComposition.TypedCoproducts.typed_distribRight_inv_hom,
      ``FailureOfComposition.TypedCoproducts.codedProgramCategoryDistributive,
      ``FailureOfComposition.TypedCoproducts.pa_proves_not_coprodIndex_invalidTag] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex ||
      n == ``FailureOfComposition.UnaryPartrec ||
      n == ``FailureOfComposition.TypedProgramCategory.ArrowPrfEq ||
      n == ``FailureOfComposition.UniformIndexQuotient.PrfEq ||
      n == ``CategoryTheory.RestrictionCategory.Split
    unless forbidden.isEmpty do
      throwError "Forbidden typed-coproduct dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected typed-coproduct axioms: {unexpected}"
    logInfo m!"Typed coproduct result {root}: {deps.size} declarations; \
      no pointwise/generated quotient, numerical proof presentation, split \
      restriction, consistency, or sorryAx dependency; axioms {axioms}."

run_cmd do
  let root := ``FailureOfComposition.ProgramIndices.no_index_quotient_via_productiveness
  let deps := collectDependencies (← getEnv) [root]
  let forbidden := deps.toArray.filter fun n =>
    n.toString.endsWith "consistent_unprovable" || n.toString.endsWith "con_unprovable" ||
    n.toString == "sorryAx"
  unless forbidden.isEmpty do
    throwError "Forbidden dependencies: {forbidden}"
  logInfo m!"Productiveness proof: traversed {deps.size} declarations; \
    no consistent_unprovable, con_unprovable, or sorryAx dependency."

run_cmd do
  let env ← getEnv
  let roots := [``FailureOfComposition.ConcreteEvaluator.evalnCertificateFormula_natCode_persist,
    ``FailureOfComposition.ConcreteEvaluator.eventualGraph_functional,
    ``FailureOfComposition.ConcreteEvaluator.eventualGraph_composition,
    ``FailureOfComposition.ConcreteEvaluator.eventualGraph_identity,
    ``FailureOfComposition.ConcreteEvaluator.eventualGraph_empty,
    ``FailureOfComposition.canonicalPartrecGraphFormula_eval_certificate_iff,
    ``FailureOfComposition.canonicalPartrecGraphFormula_eval_iff_eventualGraph,
    ``FailureOfComposition.firstSuccessGraph_uniform_eventualGraph,
    ``FailureOfComposition.ConcreteEvaluator.stageComputation_iff_evaln,
    ``FailureOfComposition.ConcreteEvaluator.eventualGraph_adequate,
    ``FailureOfComposition.ConcreteEvaluator.eventualGraph_rfind_code_eval,
    ``FailureOfComposition.ArithmeticCodeCompiler.computes_compile,
    ``FailureOfComposition.ArithmeticCodeCompiler.unaryCompile_realizes,
    ``FailureOfComposition.ConcreteIndices.guardIndex_realizes,
    ``FailureOfComposition.ConcreteIndices.searchIndex_realizes,
    ``FailureOfComposition.ConcreteIndices.no_index_quotient_via_productiveness,
    ``FailureOfComposition.ConcreteIndices.no_index_quotient_of_delta_one,
    ``FailureOfComposition.ConcreteIndices.no_index_quotient_of_re_axioms,
    ``FailureOfComposition.ConcreteIndices.no_index_quotient_of_axiom_enumerator,
    ``FailureOfComposition.ConcreteNormalForm.normalFormGraph_realizes,
    ``FailureOfComposition.ConcreteNormalForm.computationPredicate_nat,
    ``FailureOfComposition.SigmaOneRealization.semidecision_exists,
    ``FailureOfComposition.SigmaOneRealization.realize_graph,
    ``FailureOfComposition.CraigPresentation.exists_craig_presentation,
    ``FailureOfComposition.theorem_codes_re_of_axiom_codes]
  for root in roots do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString.contains "Arithmetization" || n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" || n.toString.endsWith "con_unprovable"
    unless forbidden.isEmpty do
      throwError "Forbidden concrete-evaluator dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected concrete-evaluator axioms: {unexpected}"
    logInfo m!"Concrete result {root}: {deps.size} declarations; \
      no Arithmetization, Godel-II, or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  let roots := [``FailureOfComposition.ConcreteIndices.no_index_quotient_via_godel,
    ``FailureOfComposition.ConcreteIndices.no_index_quotient_via_godel_of_re_axioms,
    ``FailureOfComposition.ConcreteIndices.no_index_quotient_via_godel_of_axiom_enumerator]
  for root in roots do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString.toLower.contains "productive" || n.toString == "sorryAx"
    unless forbidden.isEmpty do
      throwError "Forbidden Godel-II dependencies: {forbidden}"
    unless deps.toArray.any (fun n => n.toString.endsWith "consistent_unprovable") do
      throwError "Godel-II proof does not use the audited second-incompleteness theorem"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected Godel-II axioms: {unexpected}"
    logInfo m!"Godel-II result {root}: {deps.size} declarations; \
      uses consistent_unprovable; no productiveness or sorryAx dependency; \
      axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.ConcreteEvaluator.arithmetization,
      ``FailureOfComposition.ConcreteTransport.toConcrete_uniform,
      ``FailureOfComposition.ConcreteTransport.quotientEquiv,
      ``FailureOfComposition.ConcreteTransport.toConcrete_composition] do
    let deps := collectDependencies env [root]
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected representation-transport axioms: {unexpected}"
    logInfo m!"Representation result {root}: {deps.size} declarations; standard axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.PiOneCharacterization.rightCompatible_implies_piOneComplete,
      ``FailureOfComposition.PiOneCharacterization.pointwise_iff_extensional,
      ``FailureOfComposition.PiOneCharacterization.characterization,
      ``FailureOfComposition.ProgramIndices.characterization,
      ``FailureOfComposition.ConcreteIndices.pi_one_characterization,
      ``FailureOfComposition.ConcreteIndices.no_index_quotient_iff_not_piOneComplete] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" || n.toString.toLower.contains "productive" ||
      n.toString.endsWith "consistent_unprovable" || n.toString.endsWith "con_unprovable"
    unless forbidden.isEmpty do
      throwError "Forbidden characterization dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected characterization axioms: {unexpected}"
    logInfo m!"Characterization result {root}: {deps.size} declarations; \
      no productiveness, Godel-II, or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.GeneratedWitnessGraphs.AGraph_pointwise_B,
      ``FailureOfComposition.GeneratedCongruence.extensional_implies_generated,
      ``FailureOfComposition.GeneratedCongruence.classification,
      ``FailureOfComposition.ProgramIndices.generatedRel_iff_graph,
      ``FailureOfComposition.ProgramIndices.generated_congruence_classification,
      ``FailureOfComposition.ProgramIndices.generatedQuotientMulEquiv,
      ``FailureOfComposition.ConcreteIndices.generated_congruence_classification,
      ``FailureOfComposition.ConcreteIndices.pa_generated_iff_extensional,
      ``FailureOfComposition.ConcreteIndices.generated_quotient_subsingleton_iff_not_sound] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" || n.toString.toLower.contains "productive" ||
      n.toString.endsWith "consistent_unprovable" || n.toString.endsWith "con_unprovable" ||
      n.toString.endsWith ".PiOneComplete"
    unless forbidden.isEmpty do
      throwError "Forbidden generated-congruence dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected generated-congruence axioms: {unexpected}"
    logInfo m!"Generated congruence result {root}: {deps.size} declarations; \
      no productiveness, Godel-II, PiOneComplete, or sorryAx dependency; \
      axioms {axioms}."

-- Concrete weak totality, domain totality, and the conservativity consequence.
run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.ConcreteIndices.weaklyTotalIndex_identity,
      ``FailureOfComposition.ConcreteIndices.index_four_witnesses_of_history_divergence,
      ``FailureOfComposition.ConcreteIndices.weak_totality_counterexample_of_re_axioms,
      ``FailureOfComposition.ConcreteIndices.weak_totality_counterexample_of_axiom_enumerator,
      ``FailureOfComposition.ConcreteIndices.no_quotient_weak_totality_of_re_axioms,
      ``FailureOfComposition.ConcreteIndices.domainIndex_realizes,
      ``FailureOfComposition.ConcreteIndices.rTotal_of_pointwise_identity,
      ``FailureOfComposition.ConcreteIndices.exists_rTotal_not_weaklyTotal_of_re_axioms,
      ``FailureOfComposition.ConcreteIndices.pa_exists_rTotal_not_weaklyTotal,
      ``FailureOfComposition.ConcreteIndices.insert_provable_iff_of_provable,
      ``FailureOfComposition.ConcreteIndices.guard_convergenceAt_provable,
      ``FailureOfComposition.ConcreteIndices.montagna_condition_two_not_one,
      ``FailureOfComposition.ConcreteIndices.not_montagna_condition_two_implies_one] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" || n.toString.contains "Arithmetization" ||
      n.toString.endsWith "consistent_unprovable" || n.toString.endsWith "con_unprovable"
    unless forbidden.isEmpty do
      throwError "Forbidden weak-totality dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected weak-totality axioms: {unexpected}"
    logInfo m!"Weak-totality result {root}: {deps.size} declarations; \
      no Arithmetization, Godel-II, or sorryAx dependency; axioms {axioms}."

-- Concrete range assignment, witnesses, and the two proof routes.

run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.ConcreteIndices.rangeOfGraph_functional,
      ``FailureOfComposition.ConcreteIndices.uniform_rangeOfGraph,
      ``FailureOfComposition.ConcreteIndices.rangeIndex_realizes,
      ``FailureOfComposition.ConcreteIndices.rangeIndex_graph_equation,
      ``FailureOfComposition.ConcreteIndices.rangeIndex_eval,
      ``FailureOfComposition.ConcreteIndices.rangeIndex_empty,
      ``FailureOfComposition.ConcreteIndices.rangeIndex_choice_independent,
      ``FailureOfComposition.ConcreteIndices.probeIndex_realizes,
      ``FailureOfComposition.ConcreteIndices.probeIndex_pointwise_empty,
      ``FailureOfComposition.ConcreteIndices.range_probe_at_zero,
      ``FailureOfComposition.ConcreteIndices.range_probe_empty_implies_absence,
      ``FailureOfComposition.ConcreteIndices.range_counterexample_of_instance_refutations,
      ``FailureOfComposition.ConcreteIndices.no_quotient_range_of_instance_refutations,
      ``FailureOfComposition.ConcreteIndices.no_quotient_range_of_correct_assignment] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.contains "Arithmetization" ||
      n.toString.toLower.contains "productive" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable"
    unless forbidden.isEmpty do
      throwError "Forbidden Range foundation dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected Range foundation axioms: {unexpected}"
    logInfo m!"Range foundation result {root}: {deps.size} declarations; \
      no productiveness, Godel-II, Arithmetization, or sorryAx dependency; \
      axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.ConcreteIndices.proofBotPredicate_absence_unprovable,
      ``FailureOfComposition.ConcreteIndices.range_counterexample_via_godel,
      ``FailureOfComposition.ConcreteIndices.no_index_quotient_range_via_godel,
      ``FailureOfComposition.ConcreteIndices.range_counterexample_of_re_axioms,
      ``FailureOfComposition.ConcreteIndices.no_index_quotient_range_of_re_axioms,
      ``FailureOfComposition.ConcreteIndices.range_counterexample_of_axiom_enumerator,
      ``FailureOfComposition.ConcreteIndices.no_index_quotient_range_of_axiom_enumerator,
      ``FailureOfComposition.ConcreteIndices.pa_range_counterexample,
      ``FailureOfComposition.ConcreteIndices.pa_no_index_quotient_range] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.contains "Arithmetization" ||
      n.toString.toLower.contains "productive"
    unless forbidden.isEmpty do
      throwError "Forbidden Range Godel-II dependencies: {forbidden}"
    unless deps.toArray.any (fun n => n.toString.endsWith "consistent_unprovable") do
      throwError "Range Godel-II proof does not use the audited second-incompleteness theorem"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected Range Godel-II axioms: {unexpected}"
    logInfo m!"Range Godel-II result {root}: {deps.size} declarations; \
      uses consistent_unprovable; no productiveness, Arithmetization, or sorryAx \
      dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.ConcreteIndices.range_counterexample_via_productiveness,
      ``FailureOfComposition.ConcreteIndices.range_counterexample_via_productiveness_of_re_axioms,
      ``range_counterexample_via_productiveness_of_axiom_enumerator,
      ``no_index_quotient_range_via_productiveness_of_re_axioms] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.contains "Arithmetization" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable"
    unless forbidden.isEmpty do
      throwError "Forbidden Range productive dependencies: {forbidden}"
    unless deps.contains ``FailureOfComposition.productive_escape_re &&
        deps.contains ``FailureOfComposition.diagonal_escape do
      throwError "Range productive proof does not use the productive diagonal escape theorem"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected Range productive axioms: {unexpected}"
    logInfo m!"Range productive result {root}: {deps.size} declarations; \
      uses diagonal-complement productiveness; no Godel-II, Arithmetization, or \
      sorryAx dependency; axioms {axioms}."

-- Final manuscript coverage: uniform witnesses, true-Pi-one theory, and the extensional monoid.

run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.ConcreteIndices.uniformKleeneSentence_iff_uniformSentence,
      ``FailureOfComposition.ConcreteIndices.uniformIndex_iff_kleene,
      ``FailureOfComposition.ConcreteIndices.identity_comp_uniformIndex,
      ``FailureOfComposition.ConcreteIndices.guard_search_uniformIndex_empty,
      ``FailureOfComposition.ConcreteIndices.obstruction_four_properties_of_re_axioms,
      ``FailureOfComposition.ConcreteIndices.obstruction_four_properties_of_axiom_enumerator] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" || n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable"
    unless forbidden.isEmpty do
      throwError "Forbidden Manuscript obstruction dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected Manuscript obstruction axioms: {unexpected}"
    logInfo m!"Manuscript obstruction result {root}: {deps.size} declarations; \
      no Godel-II or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.PiOneCharacterization.truePiOneExtension_standard_model,
      ``FailureOfComposition.PiOneCharacterization.truePiOneExtension_consistent,
      ``FailureOfComposition.PiOneCharacterization.truePiOneExtension_piOneComplete,
      ``FailureOfComposition.PiOneCharacterization.truePiOneExtension_compositionCongruence,
      ``FailureOfComposition.PiOneCharacterization.truePiOneExtension_agreesWithExtensional,
      ``FailureOfComposition.PiOneCharacterization.truePiOneExtension_theorem_codes_not_re,
      ``FailureOfComposition.PiOneCharacterization.truePiOneExtension_axiom_codes_not_re] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" || n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable"
    unless forbidden.isEmpty do
      throwError "Forbidden True-Pi-one theory dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected True-Pi-one theory axioms: {unexpected}"
    logInfo m!"True-Pi-one theory result {root}: {deps.size} declarations; \
      no Godel-II or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [``FailureOfComposition.UnaryPartrec.ofIndex_surjective,
      ``FailureOfComposition.ConcreteIndices.generatedQuotientDenotation_bijective,
      ``FailureOfComposition.ConcreteIndices.generatedQuotientPartialRecursiveEquiv,
      ``FailureOfComposition.ConcreteIndices.generatedQuotientPartialRecursiveEquiv_mk] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" || n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n.toString.toLower.contains "productive" || n.toString.endsWith ".PiOneComplete"
    unless forbidden.isEmpty do
      throwError "Forbidden Partial-recursive quotient dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected Partial-recursive quotient axioms: {unexpected}"
    logInfo m!"Partial-recursive quotient result {root}: {deps.size} declarations; \
      no productiveness, Godel-II, PiOneComplete, or sorryAx dependency; \
      axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.TypedTuringMorphism.tauArithmeticCode_eval,
      ``FailureOfComposition.TypedTuringMorphism.tauIndex_uniform,
      ``FailureOfComposition.TypedTuringMorphism.eventualGraph_tauIndex_section_eval,
      ``FailureOfComposition.TypedTuringMorphism.eventualGraph_normalize_tauIndex_eval,
      ``FailureOfComposition.TypedTuringMorphism.eventualGraph_parameterIndex_eval,
      ``FailureOfComposition.TypedTuringMorphism.pa_proves_parameterIndex_totality,
      ``FailureOfComposition.TypedTuringMorphism.parameterArrow_isTotal,
      ``FailureOfComposition.TypedTuringMorphism.eqIndex_tauSection,
      ``FailureOfComposition.TypedTuringMorphism.eqIndex_turingFactorization,
      ``FailureOfComposition.TypedTuringMorphism.typedTau_factorization_arrowOfIndex,
      ``FailureOfComposition.TypedTuringMorphism.typedTau_isTuringMorphism,
      ``FailureOfComposition.TypedTuringMorphism.exists_factorization_coproductParameter] do
    let deps := collectDependencies env [root]
    let rawCompilerRoot :=
      root == ``FailureOfComposition.TypedTuringMorphism.tauArithmeticCode_eval ||
      root == ``FailureOfComposition.TypedTuringMorphism.tauIndex_uniform ||
      root == ``FailureOfComposition.TypedTuringMorphism.eventualGraph_tauIndex_section_eval ||
      root == ``FailureOfComposition.TypedTuringMorphism.eventualGraph_parameterIndex_eval ||
      root == ``FailureOfComposition.TypedTuringMorphism.eqIndex_tauSection
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex ||
      n == ``FailureOfComposition.UnaryPartrec ||
      n == ``FailureOfComposition.TypedProgramCategory.ArrowPrfEq ||
      n == ``FailureOfComposition.UniformIndexQuotient.PrfEq ||
      n == ``CategoryTheory.RestrictionCategory.Split ||
      n == ``CategoryTheory.RecursionCategory.PRecursionCategory ||
      n == ``CategoryTheory.RecursionCategory.Isotype ||
      n == ``CategoryTheory.RecursionCategory.Prodominical ||
      (rawCompilerRoot &&
        n == ``FailureOfComposition.SigmaOneRealization.realize_graph)
    unless forbidden.isEmpty do
      throwError "Forbidden typed-Turing dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected typed-Turing axioms: {unexpected}"
    logInfo m!"Typed Turing result {root}: {deps.size} declarations; \
      raw compiler roots exclude selected realization, while typed roots may use the \
      accepted object normalizer; no recursion-category packaging, \
      pointwise/generated quotient, consistency, or sorryAx dependency; \
      axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.TypedRecursionCategory.codedProgramCategoryHasZeroMorphisms,
      ``FailureOfComposition.TypedRecursionCategory.codedProgramCategoryProdominical,
      ``FailureOfComposition.TypedRecursionCategory.omegaProductIso,
      ``FailureOfComposition.TypedRecursionCategory.eqIndex_omegaCoprod_encode_decode,
      ``FailureOfComposition.TypedRecursionCategory.eqIndex_omegaCoprod_decode_encode,
      ``FailureOfComposition.TypedRecursionCategory.omegaCoprodIso,
      ``FailureOfComposition.TypedRecursionCategory.isoToOmega,
      ``FailureOfComposition.TypedRecursionCategory.codedProgramCategoryIsotype,
      ``FailureOfComposition.TypedRecursionCategory.codedProgramCategoryPRecursionCategory,
      ``FailureOfComposition.TypedRecursionCategory.nestedObjectIsoToOmega,
      ``FailureOfComposition.TypedRecursionCategory.codedProgramCategory_tau_isTuringMorphism] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex ||
      n == ``FailureOfComposition.UnaryPartrec ||
      n == ``FailureOfComposition.TypedProgramCategory.ArrowPrfEq ||
      n == ``FailureOfComposition.UniformIndexQuotient.PrfEq ||
      n == ``CategoryTheory.RestrictionCategory.Split
    unless forbidden.isEmpty do
      throwError "Forbidden typed-recursion-category dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected typed-recursion-category axioms: {unexpected}"
    logInfo m!"Typed recursion-category result {root}: {deps.size} declarations; \
      no pointwise/generated quotient, numerical proof presentation, split \
      restriction, consistency, or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.TypedChoice.pa_proves_sectionIndex_soundness,
      ``FailureOfComposition.TypedChoice.pa_proves_sectionIndex_domain,
      ``FailureOfComposition.TypedChoice.pa_proves_typedSectionIndex_support,
      ``FailureOfComposition.TypedChoice.typedSectionIndex_normalize_eq,
      ``FailureOfComposition.TypedChoice.eqIndex_section_comp,
      ``FailureOfComposition.TypedChoice.eqIndex_comp_section_comp,
      ``FailureOfComposition.TypedChoice.typedSectionArrow_isSection,
      ``FailureOfComposition.TypedChoice.codedProgramCategoryHasChoice,
      ``FailureOfComposition.TypedChoice.typedSectionArrow_rst_eq_ran,
      ``FailureOfComposition.TypedChoice.codedProgramCategory_hasTotalRangeLifting,
      ``FailureOfComposition.TypedChoice.codedProgramCategoryHasWeakChoice,
      ``FailureOfComposition.TypedChoice.inverseGraph_constantZero_has_two_preimages,
      ``FailureOfComposition.TypedChoice.omegaConstantZeroSection_isSection] do
    let deps := collectDependencies env [root]
    let rawSearchRoot :=
      root == ``FailureOfComposition.TypedChoice.pa_proves_sectionIndex_soundness ||
      root == ``FailureOfComposition.TypedChoice.pa_proves_sectionIndex_domain
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex ||
      n == ``FailureOfComposition.UnaryPartrec ||
      n == ``FailureOfComposition.TypedProgramCategory.ArrowPrfEq ||
      n == ``FailureOfComposition.UniformIndexQuotient.PrfEq ||
      n == ``CategoryTheory.RestrictionCategory.Split ||
      (rawSearchRoot &&
        (n == ``FailureOfComposition.SigmaOneRealization.realize_graph ||
          n == ``FailureOfComposition.SigmaOneRealization.realize_of_semidecides ||
          n == ``FailureOfComposition.SigmaOneSearch.candidateSearch_of_functional))
    unless forbidden.isEmpty do
      throwError "Forbidden typed-choice dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected typed-choice axioms: {unexpected}"
    logInfo m!"Typed choice result {root}: {deps.size} declarations; \
      raw search roots avoid graph realization and the functionality-only candidate \
      theorem, while all roots avoid pointwise/generated quotients, numerical proof \
      presentation, split restriction, consistency, and sorryAx; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.NumericalProductProofs.pa_proves_definednessEquivalence,
      ``FailureOfComposition.NumericalProductProofs.productAxiomShape_iff,
      ``FailureOfComposition.NumericalProductProofs.primrec_productAxiomTest,
      ``FailureOfComposition.NumericalProductProofs.productProof_T_meaning_sound,
      ``FailureOfComposition.NumericalProductProofs.productProofGraph_nat_iff,
      ``FailureOfComposition.NumericalProductProofs.proof_T_project0ToPair,
      ``FailureOfComposition.NumericalProductProofs.proof_T_componentsToPair,
      ``FailureOfComposition.NumericalProductProofs.provable_PA_uniformProject0ToPairPreservation,
      ``FailureOfComposition.NumericalProductProofs.provable_PA_uniformComponentsToPairPreservation,
      ``theory_provable_definedness_iff_exists_product_proof_T,
      ``FailureOfComposition.NumericalProductProofs.reTheoryProductProofGraph_nat_iff,
      ``reTheory_provable_definedness_iff_exists_product_proof_T,
      ``FailureOfComposition.NumericalProductProofs.provable_T_reTheoryProject0ToPairPreservation,
      ``FailureOfComposition.NumericalProductProofs.provable_T_reTheoryComponentsToPairPreservation,
      ``FailureOfComposition.NumericalProductProofs.typedPairRepresentative_arrow,
      ``FailureOfComposition.NumericalProductProofs.typedProject0Representative_arrow,
      ``FailureOfComposition.NumericalProductProofs.reTheory_typedProject0ToPair,
      ``FailureOfComposition.NumericalProductProofs.reTheory_omegaIdentity_product_evidence] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex ||
      n == ``FailureOfComposition.UnaryPartrec ||
      n == ``FailureOfComposition.TypedProgramCategory.ArrowPrfEq ||
      n == ``FailureOfComposition.UniformIndexQuotient.PrfEq ||
      n == ``FailureOfComposition.TypedChoice.sectionIndex ||
      n == ``CategoryTheory.RecursionCategory.PRecursionCategory
    unless forbidden.isEmpty do
      throwError "Forbidden numerical-product-proof dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected numerical-product-proof axioms: {unexpected}"
    logInfo m!"Numerical product-proof result {root}: {deps.size} declarations; \
      no choice-search, recursion-category packaging, pointwise/generated quotient, \
      consistency, or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.NumericalDomainOrder.domainOrderAxiomShape_iff,
      ``FailureOfComposition.NumericalDomainOrder.primrec_domainOrderAxiomTest,
      ``FailureOfComposition.NumericalDomainOrder.proof_T_domainOrderTransfer,
      ``FailureOfComposition.NumericalDomainOrder.primrec_domainOrderTransfer,
      ``FailureOfComposition.NumericalDomainOrder.provable_PA_meaning_domainOrder,
      ``FailureOfComposition.NumericalDomainOrder.domainOrderProofGraph_nat_iff,
      ``provable_PA_uniformDomainOrderTransferPreservation,
      ``reTheory_provable_uniform_iff_exists_domainOrderProof_T,
      ``reTheory_provable_right_iff_exists_domainOrderProof_T,
      ``provable_T_reTheoryDomainOrderTransferPreservation,
      ``FailureOfComposition.NumericalDomainOrder.pa_proves_normalizedOmegaIndex_support,
      ``FailureOfComposition.NumericalDomainOrder.classOf_normalizedOmegaIndex_comp,
      ``FailureOfComposition.NumericalDomainOrder.provableAt_of_domainOrder,
      ``FailureOfComposition.NumericalDomainOrder.mixedEquality_of_domainOrder,
      ``FailureOfComposition.NumericalDomainOrder.exists_domainOrderTransferEvidence,
      ``FailureOfComposition.NumericalDomainOrder.reTheory_identityZero_domainOrderEvidence] do
    let deps := collectDependencies env [root]
    let schemaIndependentRoot :=
      root == ``FailureOfComposition.NumericalDomainOrder.domainOrderAxiomShape_iff ||
      root == ``FailureOfComposition.NumericalDomainOrder.primrec_domainOrderAxiomTest ||
      root == ``FailureOfComposition.NumericalDomainOrder.proof_T_domainOrderTransfer ||
      root == ``FailureOfComposition.NumericalDomainOrder.primrec_domainOrderTransfer ||
      root == ``FailureOfComposition.NumericalDomainOrder.provable_PA_meaning_domainOrder ||
      root == ``FailureOfComposition.NumericalDomainOrder.pa_proves_normalizedOmegaIndex_support ||
      root == ``FailureOfComposition.NumericalDomainOrder.classOf_normalizedOmegaIndex_comp ||
      root == ``FailureOfComposition.NumericalDomainOrder.provableAt_of_domainOrder ||
      root == ``FailureOfComposition.NumericalDomainOrder.mixedEquality_of_domainOrder
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex ||
      n == ``FailureOfComposition.UniformIndexQuotient.PrfEq ||
      n == ``FailureOfComposition.TypedProgramCategory.ArrowPrfEq ||
      (schemaIndependentRoot &&
        n == ``FailureOfComposition.NumericalProductProofs.definednessTag) ||
      n == ``CategoryTheory.RecursionCategory.PRecursionCategory
    unless forbidden.isEmpty do
      throwError "Forbidden numerical-domain-order dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected numerical-domain-order axioms: {unexpected}"
    logInfo m!"Numerical domain-order result {root}: {deps.size} declarations; \
      schema-independent roots avoid definednessTag, and every root avoids old \
      PrfEq relabeling, recursion-category packaging, pointwise/generated \
      quotients, consistency, and sorryAx; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.FiniteFunctionCoding.finiteEntryFormula_eval,
      ``FailureOfComposition.FiniteFunctionCoding.finiteEntryModel_functional,
      ``FailureOfComposition.FiniteFunctionCoding.finiteEntryFormula_numeral_iff,
      ``FailureOfComposition.FiniteFunctionCoding.primrecPred_finiteEntry,
      ``FailureOfComposition.FiniteFunctionCoding.finiteEntry_competing_zero,
      ``FailureOfComposition.FiniteFunctionCoding.not_finiteEntry_competing_one] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n == ``Metamath.Feferman.codePair ||
      n == ``Arith.Feferman.Structural.codePairGraph ||
      n == ``FailureOfComposition.UniformIndexQuotient.EqIndex ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel
    unless forbidden.isEmpty do
      throwError "Forbidden finite-function-coding dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected finite-function-coding axioms: {unexpected}"
    logInfo m!"Finite-function coding result {root}: {deps.size} declarations; \
      no bit-interleaving proof-code pair, quotient relation, or sorryAx dependency; \
      axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.FiniteFunctionEvaluator.alphaGraph_functional,
      ``FailureOfComposition.FiniteFunctionEvaluator.alphaIndex_uniform,
      ``FailureOfComposition.FiniteFunctionEvaluator.eventualGraph_alphaIndex_pair_eval,
      ``FailureOfComposition.FiniteFunctionEvaluator.alphaIndex_computes_iff,
      ``FailureOfComposition.FiniteFunctionEvaluator.pa_proves_alphaIndex_support,
      ``FailureOfComposition.FiniteFunctionEvaluator.eqIndex_normalize_alphaIndex,
      ``FailureOfComposition.FiniteFunctionEvaluator.eventualGraph_normalize_alphaIndex_eval,
      ``FailureOfComposition.FiniteFunctionEvaluator.alphaArrow_val] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex ||
      n == ``FailureOfComposition.UnaryPartrec ||
      n == ``FailureOfComposition.TypedProgramCategory.ArrowPrfEq ||
      n == ``FailureOfComposition.UniformIndexQuotient.PrfEq ||
      n == ``CategoryTheory.RestrictionCategory.Split ||
      n == ``CategoryTheory.RecursionCategory.PRecursionCategory ||
      n.toString.startsWith
        "FailureOfComposition.NumericalProductProofs"
    unless forbidden.isEmpty do
      throwError "Forbidden finite-function-evaluator dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected finite-function-evaluator axioms: {unexpected}"
    logInfo m!"Finite-function evaluator result {root}: {deps.size} declarations; \
      no numerical product-proof presentation, recursion-category packaging, \
      pointwise/generated quotient, consistency, or sorryAx dependency; \
      axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.FiniteExtensionChecker.extensionFormula_numeral_eval_iff,
      ``FailureOfComposition.FiniteExtensionChecker.proves_extensionFormula_iff_preceq,
      ``FailureOfComposition.FiniteExtensionChecker.zeroTestIndex_uniform,
      ``FailureOfComposition.FiniteExtensionChecker.extensionCheckerIndex_uniform,
      ``FailureOfComposition.FiniteExtensionChecker.extensionCheckerArrow_eq_domainArrow,
      ``FailureOfComposition.FiniteExtensionChecker.proves_zeroTest_iff_extension,
      ``FailureOfComposition.FiniteExtensionChecker.extensionDomain_provableAt_iff_preceq,
      ``FailureOfComposition.FiniteExtensionChecker.pa_proves_extensionFormula_one_identity] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex ||
      n.toString.startsWith
        "FailureOfComposition.NumericalExtensionProofs"
    unless forbidden.isEmpty do
      throwError "Forbidden finite-extension-checker dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected finite-extension-checker axioms: {unexpected}"
    logInfo m!"Finite-extension checker result {root}: {deps.size} declarations; \
      no numerical presentation, pointwise/generated quotient, consistency, or \
      sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.NumericalExtensionProofs.extensionAxiomShape_iff,
      ``FailureOfComposition.NumericalExtensionProofs.primrec_extensionAxiomTest,
      ``FailureOfComposition.NumericalExtensionProofs.proof_T_checkerToExt,
      ``FailureOfComposition.NumericalExtensionProofs.proof_T_extToChecker,
      ``FailureOfComposition.NumericalExtensionProofs.finiteExtensionProofGraph_nat_iff,
      ``FailureOfComposition.NumericalExtensionProofs.provable_PA_uniformCheckerToExtPreservation,
      ``FailureOfComposition.NumericalExtensionProofs.provable_PA_uniformExtToCheckerPreservation,
      ``reTheory_provable_extension_iff_exists_checkerProof_T,
      ``reTheory_provable_extension_iff_exists_extensionProof_T,
      ``FailureOfComposition.NumericalExtensionProofs.provable_T_reTheoryCheckerToExtPreservation,
      ``FailureOfComposition.NumericalExtensionProofs.reTheory_one_identity_conversion_evidence] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex ||
      n == ``CategoryTheory.RecursionCategory.PRecursionCategory
    unless forbidden.isEmpty do
      throwError "Forbidden numerical-extension-proof dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected numerical-extension-proof axioms: {unexpected}"
    logInfo m!"Numerical finite-extension result {root}: {deps.size} declarations; \
      no recursion-category packaging, pointwise/generated quotient, consistency, \
      or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.NumericalExtensionComposition.extensionCompositionAxiomShape_iff,
      ``FailureOfComposition.NumericalExtensionComposition.primrec_extensionCompositionAxiomTest,
      ``FailureOfComposition.NumericalExtensionComposition.proof_T_projectionEqualityToPair,
      ``FailureOfComposition.NumericalExtensionComposition.proof_T_projectionEqualityToLeft,
      ``FailureOfComposition.NumericalExtensionComposition.proof_T_componentValuesToChecker,
      ``FailureOfComposition.NumericalExtensionComposition.proof_T_componentValuesToExt,
      ``FailureOfComposition.NumericalExtensionComposition.primrec_projectionEqualityToPair,
      ``FailureOfComposition.NumericalExtensionComposition.primrec_projectionEqualityToLeft,
      ``FailureOfComposition.NumericalExtensionComposition.primrec_componentValuesToChecker,
      ``FailureOfComposition.NumericalExtensionComposition.primrec_componentValuesToExt,
      ``provable_PA_meaning_projectionDefinedness,
      ``provable_PA_meaning_componentValuesToChecker,
      ``FailureOfComposition.NumericalExtensionComposition.extensionCompositionProofGraph_nat_iff,
      ``provable_PA_uniformProjectionEqualityToPairPreservation,
      ``provable_PA_uniformProjectionEqualityToLeftPreservation,
      ``provable_PA_uniformComponentValuesToCheckerPreservation,
      ``provable_PA_uniformComponentValuesToExtPreservation,
      ``reTheory_provable_extension_iff_exists_extensionCompositionProof_T,
      ``provable_T_reTheoryComponentValuesToExtPreservation,
      ``FailureOfComposition.NumericalExtensionComposition.mixedEquality_of_projectionEquation,
      ``FailureOfComposition.NumericalExtensionComposition.mixedEquality_of_extensionEquation,
      ``FailureOfComposition.NumericalExtensionComposition.projectionEquation_domain_pair,
      ``FailureOfComposition.NumericalExtensionComposition.projectionEquation_domain_left,
      ``FailureOfComposition.NumericalExtensionComposition.projectionEquation_definedness_left,
      ``FailureOfComposition.NumericalExtensionComposition.extensionEquation_proves_extension,
      ``FailureOfComposition.NumericalExtensionComposition.extensionEquation_preceq,
      ``FailureOfComposition.NumericalExtensionComposition.exists_projectionEquationEvidence,
      ``FailureOfComposition.NumericalExtensionComposition.exists_extensionEquationEvidence,
      ``FailureOfComposition.NumericalExtensionComposition.pa_applicationPair_checker_eq,
      ``FailureOfComposition.NumericalExtensionComposition.application_extensionEquation,
      ``FailureOfComposition.NumericalExtensionComposition.reTheory_application_composedEvidence] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex
    unless forbidden.isEmpty do
      throwError "Forbidden numerical-extension-composition dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected numerical-extension-composition axioms: {unexpected}"
    logInfo m!"Numerical extension-composition result {root}: {deps.size} declarations; \
      no pointwise/generated quotient, consistency, or sorryAx dependency; \
      axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.NumericalExtensionTheta.primrec_thetaIndex,
      ``FailureOfComposition.NumericalExtensionTheta.extensionThetaAxiomShape_iff,
      ``FailureOfComposition.NumericalExtensionTheta.primrec_extensionThetaAxiomTest,
      ``FailureOfComposition.NumericalExtensionTheta.proof_T_componentAndCheckerToTheta,
      ``FailureOfComposition.NumericalExtensionTheta.proof_T_componentAndExtToTheta,
      ``FailureOfComposition.NumericalExtensionTheta.primrec_componentAndCheckerToTheta,
      ``FailureOfComposition.NumericalExtensionTheta.primrec_componentAndExtToTheta,
      ``FailureOfComposition.NumericalExtensionTheta.eventualGraph_thetaIndex_pair_eval,
      ``FailureOfComposition.NumericalExtensionTheta.PA_proves_theta_of_component_and_checker,
      ``FailureOfComposition.NumericalExtensionTheta.extensionThetaProofGraph_nat_iff,
      ``provable_PA_uniformComponentAndCheckerToThetaPreservation,
      ``provable_PA_uniformComponentAndExtToThetaPreservation,
      ``FailureOfComposition.NumericalExtensionTheta.reTheoryExtensionThetaProofGraph_nat_iff,
      ``FailureOfComposition.NumericalExtensionTheta.reTheoryPAProof_T_componentAndCheckerToTheta,
      ``provable_T_reTheoryComponentAndExtToThetaPreservation,
      ``FailureOfComposition.NumericalExtensionTheta.classOf_thetaRepresentative,
      ``FailureOfComposition.NumericalExtensionTheta.theta_provableAt,
      ``FailureOfComposition.NumericalExtensionTheta.exists_thetaEvidence,
      ``FailureOfComposition.NumericalExtensionTheta.applicationTheta_pair_eval,
      ``FailureOfComposition.NumericalExtensionTheta.applicationTheta_eq_p1,
      ``FailureOfComposition.NumericalExtensionTheta.reTheory_applicationThetaEvidence] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex
    unless forbidden.isEmpty do
      throwError "Forbidden numerical-extension-theta dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected numerical-extension-theta axioms: {unexpected}"
    logInfo m!"Numerical extension-theta result {root}: {deps.size} declarations; \
      no pointwise/generated quotient, consistency, or sorryAx dependency; \
      axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.NumericalRangeProofs.primrec_computationAxiomTest,
      ``FailureOfComposition.NumericalRangeProofs.primrec_rangeIntroAxiomTest,
      ``FailureOfComposition.NumericalRangeProofs.proof_T_rangeProof,
      ``FailureOfComposition.NumericalRangeProofs.primrec_rangeProof,
      ``FailureOfComposition.NumericalRangeProofs.rangeProof_T_meaning_sound,
      ``FailureOfComposition.NumericalRangeProofs.paRangeProof_correct,
      ``FailureOfComposition.NumericalRangeProofs.PA_proves_rangeFixpoint_of_stageComputation,
      ``FailureOfComposition.NumericalRangeProofs.rangeProofGraph_nat_iff,
      ``FailureOfComposition.NumericalRangeProofs.rangeProofMapGraph_total,
      ``FailureOfComposition.NumericalRangeProofs.rangeProofMapGraph_functional,
      ``FailureOfComposition.NumericalRangeProofs.rangeProofGraph_rangeProof,
      ``FailureOfComposition.NumericalRangeProofs.provable_PA_uniformRangeProofPreservation,
      ``FailureOfComposition.NumericalRangeProofs.primrec_typedRangeProof,
      ``FailureOfComposition.NumericalRangeProofs.typedRangeProof_correct,
      ``FailureOfComposition.NumericalRangeProofs.PA_proves_typedRangeFixpoint_of_stageComputation,
      ``theory_proves_typedRangeFixpoint_of_stageComputation,
      ``FailureOfComposition.NumericalRangeProofs.normalized_stageComputation_support,
      ``FailureOfComposition.NumericalRangeProofs.typedRangeProof_endpoint_is_ran] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex ||
      n.toString.startsWith
        "FailureOfComposition.NumericalExtensionComposition" ||
      n.toString.startsWith
        "FailureOfComposition.NumericalExtensionTheta" ||
      n.toString.startsWith
        "FailureOfComposition.FiniteFunctionEvaluator" ||
      n.toString.startsWith
        "FailureOfComposition.TypedTuringMorphism" ||
      n.toString.startsWith
        "FailureOfComposition.TypedRecursionCategory" ||
      n.toString.startsWith
        "FailureOfComposition.TypedChoice"
    unless forbidden.isEmpty do
      throwError "Forbidden numerical-range-proof dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected numerical-range-proof axioms: {unexpected}"
    logInfo m!"Numerical range-proof result {root}: {deps.size} declarations; \
      no unrelated later B1 construction, pointwise/generated quotient, consistency, \
      or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.ProofSearchMembership.prfEqFormula_nat_iff,
      ``FailureOfComposition.ProofSearchMembership.typedProofSearchMembershipFormula_nat_iff,
      ``FailureOfComposition.ProofSearchMembership.typedProofSearchTransferNumeral_eval,
      ``FailureOfComposition.ProofSearchMembership.exists_prfEq_transport,
      ``FailureOfComposition.ProofSearchMembership.exists_typedProofSearchMembership_of_outputs] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex ||
      n.toString.startsWith
        "FailureOfComposition.PrfEqTransportRepair" ||
      n.toString.startsWith
        "FailureOfComposition.NumericalProductProofs" ||
      n.toString.startsWith
        "FailureOfComposition.NumericalDomainOrder" ||
      n.toString.startsWith
        "FailureOfComposition.NumericalExtensionProofs" ||
      n.toString.startsWith
        "FailureOfComposition.NumericalExtensionComposition" ||
      n.toString.startsWith
        "FailureOfComposition.NumericalExtensionTheta" ||
      n.toString.startsWith
        "FailureOfComposition.NumericalRangeProofs"
    unless forbidden.isEmpty do
      throwError "Forbidden proof-search-boundary dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected proof-search-boundary axioms: {unexpected}"
    logInfo m!"Proof-search boundary {root}: {deps.size} declarations; \
      exact PrfEq only, with no enlarged B1 checker, pointwise/generated quotient, \
      consistency, or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
      ``FailureOfComposition.PrfEqTransportRepair.transportAxiomShape_iff,
      ``FailureOfComposition.PrfEqTransportRepair.primrec_transportAxiomTest,
      ``FailureOfComposition.PrfEqTransportRepair.proof_T_extended_to_transportRepair,
      ``FailureOfComposition.PrfEqTransportRepair.proof_T_transport,
      ``FailureOfComposition.PrfEqTransportRepair.primrec_transport,
      ``FailureOfComposition.PrfEqTransportRepair.prfEq_inputs_to_repairTransport,
      ``FailureOfComposition.PrfEqTransportRepair.provable_PA_meaning_transportAxiom,
      ``FailureOfComposition.PrfEqTransportRepair.repairPrfEq_to_exists_prfEq,
      ``FailureOfComposition.PrfEqTransportRepair.transportRepairProofGraph_nat_iff,
      ``FailureOfComposition.PrfEqTransportRepair.transportGraph_total,
      ``FailureOfComposition.PrfEqTransportRepair.transportGraph_functional,
      ``FailureOfComposition.PrfEqTransportRepair.transportRepairProofGraph_transport,
      ``FailureOfComposition.PrfEqTransportRepair.provable_PA_uniformTransportPreservation,
      ``FailureOfComposition.PrfEqTransportRepair.repairPrfEqFormula_nat_iff,
      ``provable_PA_reTheoryUniformTransportPreservation] do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n.toString == "sorryAx" ||
      n.toString.endsWith "consistent_unprovable" ||
      n.toString.endsWith "con_unprovable" ||
      n == ``FailureOfComposition.GeneratedCongruence.Rel ||
      n == ``FailureOfComposition.GeneratedCongruence.graphSetoid ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex ||
      n.toString.startsWith
        "FailureOfComposition.NumericalProductProofs" ||
      n.toString.startsWith
        "FailureOfComposition.NumericalDomainOrder" ||
      n.toString.startsWith
        "FailureOfComposition.NumericalExtensionProofs" ||
      n.toString.startsWith
        "FailureOfComposition.NumericalExtensionComposition" ||
      n.toString.startsWith
        "FailureOfComposition.NumericalExtensionTheta" ||
      n.toString.startsWith
        "FailureOfComposition.NumericalRangeProofs"
    unless forbidden.isEmpty do
      throwError "Forbidden PrfEq-transport-repair dependencies: {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected PrfEq-transport-repair axioms: {unexpected}"
    logInfo m!"PrfEq transport repair {root}: {deps.size} declarations; \
      additive checker only, with no later B1 checker, pointwise/generated quotient, \
      consistency, or sorryAx dependency; axioms {axioms}."

run_cmd do
  let env ← getEnv
  let graphRoots := [
    ``FailureOfComposition.NativeInternalSyntax.formulaShiftGraph,
    ``FailureOfComposition.NativeInternalSyntax.formulaFreeGraph,
    ``FailureOfComposition.NativeInternalSyntax.sequentShiftGraph,
    ``FailureOfComposition.NativeInternalChecker.ruleAccept,
    ``FailureOfComposition.NativeInternalChecker.ruleAcceptDelta,
    ``FailureOfComposition.NativeInternalChecker.ruleCheckGraph,
    ``FailureOfComposition.NativeInternalChecker.Table.blueprint,
    ``FailureOfComposition.NativeInternalChecker.Table.construction,
    ``FailureOfComposition.NativeInternalChecker.checkTableGraph,
    ``FailureOfComposition.NativeInternalGraphs.nativeDerivationCheckGraph,
    ``FailureOfComposition.NativeInternalGraphs.nativeDerivationOfCheckGraph,
    ``FailureOfComposition.NativeInternalGraphs.nativeProofCheckGraph,
    ``FailureOfComposition.NativeInternalAxiomGraph.canonicalAxiomGraph,
    ``FailureOfComposition.NativeInternalEquality.nativeEqCheckFormula]
  for root in graphRoots do
    let bodies := collectDefinitionBodies env [root]
    let semantic := bodies.toArray.filter fun n =>
      (`FFL.FirstOrder.Arithmetic.Bootstrapping.Derivation).isPrefixOf n ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.DerivationOf ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.Proof ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.derivation ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.derivationOf ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.proof
    unless semantic.isEmpty do
      throwError "Internal checker graph calls a Foundation proof predicate: {root}; {semantic}"
    logInfo m!"Structural internal checker graph {root}: {bodies.size} definition-body \
      dependencies; no Foundation derivation/proof predicate."
  let theoremRoots := [
    ``FailureOfComposition.NativeInternalApplications.canonical_checks_correct,
    ``FailureOfComposition.NativeInternalApplications.exists_craig_structural_checker,
    ``FailureOfComposition.NativeInternalApplications.craig_eq_acceptance_iff_eqIndex,
    ``FailureOfComposition.NativeInternalApplications.exists_uniform_craig_seed_acceptance,
    ``FailureOfComposition.NativeInternalEquality.nativeEqCheckFormula_iff,
    ``FailureOfComposition.NativeInternalEquality.nativeEqCheckFormula_nat_iff,
    ``FailureOfComposition.NativeInternalEquality.transportGraph_preserves_acceptance,
    ``FailureOfComposition.NativeInternalEquality.exists_uniform_seed_acceptance,
    ``FailureOfComposition.NativeInternalChecker.historyAcceptDelta_sigma_iff,
    ``FailureOfComposition.NativeInternalChecker.historyAcceptDelta_pi_iff,
    ``FailureOfComposition.NativeInternalChecker.ruleAcceptDelta_sigma_iff,
    ``FailureOfComposition.NativeInternalChecker.ruleAcceptDelta_pi_iff,
    ``FailureOfComposition.NativeInternalChecker.ruleCheckGraph_iff,
    ``FailureOfComposition.NativeInternalChecker.ruleCheckGraph_total,
    ``FailureOfComposition.NativeInternalChecker.ruleCheckGraph_functional,
    ``FailureOfComposition.NativeInternalChecker.ruleCheckValue_isBit,
    ``FailureOfComposition.NativeInternalChecker.checkTableGraph_iff,
    ``FailureOfComposition.NativeInternalChecker.checkTableValue_zero,
    ``FailureOfComposition.NativeInternalChecker.checkTableValue_succ,
    ``FailureOfComposition.NativeInternalChecker.checkTableGraph_total,
    ``FailureOfComposition.NativeInternalChecker.checkTableGraph_functional,
    ``FailureOfComposition.NativeInternalChecker.checkTableValue_seq_length,
    ``FailureOfComposition.NativeInternalChecker.checkTableValue_lookup_lt,
    ``FailureOfComposition.NativeInternalChecker.checkTableValue_lookup_last,
    ``FailureOfComposition.NativeInternalChecker.checkTableValue_bits,
    ``FailureOfComposition.NativeInternalNat.ruleAccept_nat_iff,
    ``FailureOfComposition.NativeInternalNat.ruleCheckValue_nat,
    ``FailureOfComposition.NativeInternalNat.checkTableValue_nat,
    ``FailureOfComposition.NativeInternalNat.nativeDerivationCheckGraph_nat_iff,
    ``FailureOfComposition.NativeInternalNat.nativeDerivationOfCheckGraph_nat_iff,
    ``FailureOfComposition.NativeInternalNat.nativeProofCheckGraph_nat_iff,
    ``FailureOfComposition.NativeInternalNat.invalid_axiom_leaf_rejected,
    ``FailureOfComposition.NativeInternalGraphs.nativeDerivationCheckGraph_iff,
    ``FailureOfComposition.NativeInternalGraphs.nativeDerivationOfCheckGraph_iff,
    ``FailureOfComposition.NativeInternalGraphs.nativeProofCheckGraph_iff,
    ``FailureOfComposition.NativeInternalGraphs.nativeDerivationCheckValue_isBit,
    ``FailureOfComposition.NativeInternalGraphs.nativeDerivationOfCheckValue_isBit,
    ``FailureOfComposition.NativeInternalGraphs.nativeProofCheckValue_isBit,
    ``FailureOfComposition.NativeInternalGraphs.nativeDerivationCheckGraph_existsUnique,
    ``FailureOfComposition.NativeInternalGraphs.nativeDerivationOfCheckGraph_existsUnique,
    ``FailureOfComposition.NativeInternalGraphs.nativeProofCheckGraph_existsUnique,
    ``FailureOfComposition.NativeInternalAxiomGraph.canonicalAxiomGraph_iff,
    ``FailureOfComposition.NativeInternalAxiomGraph.canonicalAxiomGraph_computational,
    ``FailureOfComposition.NativeInternalAxiomGraph.canonicalAxiomGraph_theory,
    ``FailureOfComposition.NativeInternalAxiomGraph.canonicalAxiomGraph_numerical,
    ``FailureOfComposition.NativeInternalSequence.historyCode_append,
    ``FailureOfComposition.NativeInternalSequence.historyCode_seq_length,
    ``FailureOfComposition.NativeInternalSequence.historyCode_lookup,
    ``FailureOfComposition.NativeInternalSequence.historyCode_accepts_iff,
    ``FailureOfComposition.NativeInternalSyntax.axiomBitValue_spec,
    ``FailureOfComposition.NativeInternalSyntax.axiomBitValue_eq_iff,
    ``FailureOfComposition.NativeInternalSyntax.axiomBitValue_isBit,
    ``FailureOfComposition.NativeInternalSyntax.formulaShiftGraph_iff,
    ``FailureOfComposition.NativeInternalSyntax.formulaShiftGraph_total,
    ``FailureOfComposition.NativeInternalSyntax.formulaShiftGraph_functional,
    ``FailureOfComposition.NativeInternalSyntax.formulaShiftValue_eq_shift,
    ``FailureOfComposition.NativeInternalSyntax.formulaShiftValue_eq_zero_of_invalid,
    ``FailureOfComposition.NativeInternalSyntax.formulaShiftValue_nat,
    ``FailureOfComposition.NativeInternalSyntax.formulaShiftGraph_nat_iff,
    ``FailureOfComposition.NativeInternalSyntax.formulaFreeGraph_iff,
    ``FailureOfComposition.NativeInternalSyntax.formulaFreeGraph_total,
    ``FailureOfComposition.NativeInternalSyntax.formulaFreeGraph_functional,
    ``FailureOfComposition.NativeInternalSyntax.formulaFreeValue_eq_free,
    ``FailureOfComposition.NativeInternalSyntax.formulaFreeValue_nat,
    ``FailureOfComposition.NativeInternalSyntax.formulaFreeGraph_nat_iff,
    ``FailureOfComposition.NativeInternalSyntax.mem_sequentShiftValue_iff,
    ``FailureOfComposition.NativeInternalSyntax.sequentShiftGraph_iff,
    ``FailureOfComposition.NativeInternalSyntax.sequentShiftGraph_total,
    ``FailureOfComposition.NativeInternalSyntax.sequentShiftGraph_functional,
    ``FailureOfComposition.NativeInternalSyntax.sequentShiftValue_eq_setShift,
    ``FailureOfComposition.NativeInternalSyntax.sequentShiftValue_nat,
    ``FailureOfComposition.NativeInternalSyntax.sequentShiftGraph_nat_iff,
    ``FailureOfComposition.NativeInternalCorrectness.ruleAccept_iff_derivation,
    ``FailureOfComposition.NativeInternalCorrectness.checkTableValue_history_correct,
    ``FailureOfComposition.NativeInternalCorrectness.nativeDerivationCheckValue_accepts_iff,
    ``FailureOfComposition.NativeInternalCorrectness.nativeDerivationCheckGraph_correct,
    ``FailureOfComposition.NativeInternalCorrectness.nativeDerivationOfCheckGraph_correct,
    ``FailureOfComposition.NativeInternalCorrectness.nativeProofCheckGraph_correct]
  for root in graphRoots ++ theoremRoots do
    let allowed := if (`FailureOfComposition.NativeInternalApplications).isPrefixOf root then
      nativeInternalBridgeAllowedProjectNamespaces else nativeInternalAllowedProjectNamespaces
    let deps := collectDependencies env [root]
    let forbidden := forbiddenNativeDependencies env allowed root
    unless forbidden.isEmpty do
      throwError "Forbidden structural internal checker dependencies: {root}; {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected structural internal checker axioms: {root}; {unexpected}"
    logInfo m!"Structural internal checker root {root}: {deps.size} declarations; \
      separate internal allowance; no production/repaired checker, consistency, or sorryAx; \
      axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
    ``FailureOfComposition.NativeFamilyExtraction.allBodyCode,
    ``FailureOfComposition.NativeFamilyExtraction.consequentCode,
    ``FailureOfComposition.NativeFamilyExtraction.antecedentCode,
    ``FailureOfComposition.NativeFamilyExtraction.applyCtxCode,
    ``FailureOfComposition.NativeFamilyExtraction.extractCtx,
    ``FailureOfComposition.NativeFamilyExtraction.extractCtxPacked,
    ``FailureOfComposition.NativeFamilyExtraction.unaryInstanceCode,
    ``FailureOfComposition.NativeFamilyExtraction.binaryInstanceCode] do
    if isNoncomputable env root then
      throwError "Noncomputable family numerical constructor: {root}"
    let directClassical := directClassicalDependencies env root
    let bodies := collectDefinitionBodies env [root]
    let classical := bodies.toArray.filter fun n => `Classical |>.isPrefixOf (privateToUserName n)
    unless directClassical.isEmpty && classical.isEmpty do
      throwError "Choice/Classical dependency in family numerical body: {root}; {classical}"
    let forbidden := forbiddenNativeDependencies env nativeFamilyNumericalAllowedProjectNamespaces root
    unless forbidden.isEmpty do
      throwError "Forbidden numerical family dependencies: {root}; {forbidden}"
    logInfo m!"Family numerical constructor {root}: computable; no Classical body closure; \
      separate numerical allowance; no production checker or consistency dependency."

run_cmd do
  let env ← getEnv
  let graphRoots := [
    ``FailureOfComposition.NativeFamilyExtraction.programGraph,
    ``FailureOfComposition.NativeFamilyExtraction.outputGraph,
    ``FailureOfComposition.NativeFamilyExtraction.familyGraph,
    ``FailureOfComposition.NativeFamilyExtraction.antecedentGraph,
    ``FailureOfComposition.NativeFamilyExtraction.consequentGraph,
    ``FailureOfComposition.NativeFamilyExtraction.applyCtxGraph,
    ``FailureOfComposition.NativeFamilyExtraction.extractGraph,
    ``FailureOfComposition.NativeFamilyExtraction.unaryInstanceGraph,
    ``FailureOfComposition.NativeFamilyExtraction.binaryInstanceGraph]
  for root in graphRoots do
    let bodies := collectDefinitionBodies env [root]
    let semantic := bodies.toArray.filter fun n =>
      (`FFL.FirstOrder.Arithmetic.Bootstrapping.Derivation).isPrefixOf n ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.DerivationOf ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.Proof ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.derivation ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.derivationOf ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.proof
    unless semantic.isEmpty do
      throwError "Family graph calls a Foundation proof predicate: {root}; {semantic}"
    logInfo m!"Structural family graph {root}: {bodies.size} definition-body dependencies; \
      no Foundation derivation/proof predicate."
  let theoremRoots := [
    ``FailureOfComposition.NativeFamilyExtraction.programGraph_eval,
    ``FailureOfComposition.NativeFamilyExtraction.outputGraph_eval,
    ``FailureOfComposition.NativeFamilyExtraction.outputGraph_programGraph,
    ``FailureOfComposition.NativeFamilyExtraction.familyGraph_eval,
    ``FailureOfComposition.NativeFamilyExtraction.familyEq_eval,
    ``FailureOfComposition.NativeFamilyExtraction.equalityFormula_eval,
    ``FailureOfComposition.NativeFamilyExtraction.extractionMatrix_eval,
    ``FailureOfComposition.NativeFamilyExtraction.extractionMatrix_valid,
    ``FailureOfComposition.NativeFamilyExtraction.extractionSeed_provable,
    ``FailureOfComposition.NativeFamilyExtraction.toNumVec_instance,
    ``FailureOfComposition.NativeFamilyExtraction.instanceValue_nat,
    ``FailureOfComposition.NativeFamilyExtraction.exists_accepted_sigma_instance,
    ``FailureOfComposition.NativeFamilyExtraction.exists_canonical_sigma_instance,
    ``FailureOfComposition.NativeFamilyExtraction.consequentGraph_iff,
    ``FailureOfComposition.NativeFamilyExtraction.antecedentGraph_iff,
    ``FailureOfComposition.NativeFamilyExtraction.applyCtxGraph_iff,
    ``FailureOfComposition.NativeFamilyExtraction.extractGraph_iff,
    ``FailureOfComposition.NativeFamilyExtraction.extractGraph_total,
    ``FailureOfComposition.NativeFamilyExtraction.extractGraph_functional,
    ``FailureOfComposition.NativeFamilyExtraction.allBodyValue_all,
    ``FailureOfComposition.NativeFamilyExtraction.consequentValue_imp,
    ``FailureOfComposition.NativeFamilyExtraction.antecedentValue_imp,
    ``FailureOfComposition.NativeFamilyExtraction.primrec_allBodyCode,
    ``FailureOfComposition.NativeFamilyExtraction.primrec_consequentCode,
    ``FailureOfComposition.NativeFamilyExtraction.primrec_antecedentCode,
    ``FailureOfComposition.NativeFamilyExtraction.primrec_extractCtxPacked,
    ``FailureOfComposition.NativeFamilyExtraction.allBodyValue_nat,
    ``FailureOfComposition.NativeFamilyExtraction.consequentValue_nat,
    ``FailureOfComposition.NativeFamilyExtraction.antecedentValue_nat,
    ``FailureOfComposition.NativeFamilyExtraction.applyCtxValue_nat,
    ``FailureOfComposition.NativeFamilyExtraction.extractValue_nat,
    ``FailureOfComposition.NativeFamilyExtraction.extractGraph_nat_iff,
    ``FailureOfComposition.NativeFamilyExtraction.seedBody_quote,
    ``FailureOfComposition.NativeFamilyExtraction.seed_quote,
    ``FailureOfComposition.NativeFamilyExtraction.subst1Value_typedNumeral,
    ``FailureOfComposition.NativeFamilyExtraction.first_specialization,
    ``FailureOfComposition.NativeFamilyExtraction.second_specialization,
    ``FailureOfComposition.NativeFamilyExtraction.third_specialization,
    ``FailureOfComposition.NativeFamilyExtraction.instanceValue_imp,
    ``FailureOfComposition.NativeFamilyExtraction.instanceValue_rew,
    ``FailureOfComposition.NativeFamilyExtraction.matrix_instance,
    ``FailureOfComposition.NativeFamilyExtraction.exists_standard_extraction_seed,
    ``FailureOfComposition.NativeFamilyExtraction.derivationOf_specializeNumeral,
    ``FailureOfComposition.NativeFamilyExtraction.derivationOf_applyCtxValue,
    ``FailureOfComposition.NativeFamilyExtraction.derivationOf_extractValue,
    ``FailureOfComposition.NativeFamilyExtraction.extractGraph_preserves_derivationOf,
    ``FailureOfComposition.NativeFamilyExtraction.proof_extractValue,
    ``FailureOfComposition.NativeFamilyExtraction.primrec₂_unaryInstanceCode,
    ``FailureOfComposition.NativeFamilyExtraction.primrec_binaryInstanceCode,
    ``FailureOfComposition.NativeFamilyExtraction.unaryInstanceGraph_iff,
    ``FailureOfComposition.NativeFamilyExtraction.binaryInstanceGraph_iff,
    ``FailureOfComposition.NativeFamilyExtraction.unaryInstanceGraph_existsUnique,
    ``FailureOfComposition.NativeFamilyExtraction.binaryInstanceGraph_existsUnique,
    ``FailureOfComposition.NativeFamilyExtraction.unaryInstance_literal,
    ``FailureOfComposition.NativeFamilyExtraction.binaryInstance_literal,
    ``FailureOfComposition.NativeFamilyExtraction.unaryInstanceGraph_nat_iff,
    ``FailureOfComposition.NativeFamilyExtraction.binaryInstanceGraph_nat_iff,
    ``FailureOfComposition.NativeFamilyExtraction.unaryInstanceCode_encode,
    ``FailureOfComposition.NativeFamilyExtraction.binaryInstanceCode_encode,
    ``FailureOfComposition.NativeFamilyExtraction.extractGraph_preserves_acceptance,
    ``FailureOfComposition.NativeFamilyExtraction.exists_extraction_endpoint,
    ``FailureOfComposition.NativeFamilyExtraction.exists_output_equality,
    ``FailureOfComposition.NativeFamilyExtraction.exists_family_transport,
    ``FailureOfComposition.NativeFamilyExtraction.exists_typed_family_transport,
    ``FailureOfComposition.NativeFamilyExtraction.exists_craig_family_transport]
  let arithmeticRoots := [
    ``FailureOfComposition.NativeFamilyExtraction.extractionMatrix_valid,
    ``FailureOfComposition.NativeFamilyExtraction.extractionSeed_provable,
    ``FailureOfComposition.NativeFamilyExtraction.exists_standard_extraction_seed,
    ``FailureOfComposition.NativeFamilyExtraction.exists_extraction_endpoint,
    ``FailureOfComposition.NativeFamilyExtraction.exists_output_equality,
    ``FailureOfComposition.NativeFamilyExtraction.exists_family_transport,
    ``FailureOfComposition.NativeFamilyExtraction.exists_craig_family_transport]
  for root in graphRoots ++ theoremRoots do
    let allowed := if root == ``FailureOfComposition.NativeFamilyExtraction.exists_typed_family_transport
      then nativeFamilyTypedAllowedProjectNamespaces
      else if arithmeticRoots.contains root then nativeFamilyArithmeticAllowedProjectNamespaces
      else nativeFamilyInternalAllowedProjectNamespaces
    let forbidden := forbiddenNativeDependencies env allowed root
    unless forbidden.isEmpty do
      throwError "Forbidden family extraction dependencies: {root}; {forbidden}"
    let deps := collectDependencies env [root]
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected family extraction axioms: {root}; {unexpected}"
    logInfo m!"Family extraction root {root}: {deps.size} declarations; separate family allowance; \
      no production/repaired checker, consistency, or sorryAx; axioms {axioms}."

run_cmd do
  let env ← getEnv
  for root in [
    ``FailureOfComposition.NativeMembershipAssembly.pointwiseCtx,
    ``FailureOfComposition.NativeMembershipAssembly.pointwiseCtxPacked,
    ``FailureOfComposition.NativeMembershipAssembly.closureCtx,
    ``FailureOfComposition.NativeMembershipAssembly.closureCtxPacked] do
    if isNoncomputable env root then
      throwError "Noncomputable membership numerical constructor: {root}"
    let directClassical := directClassicalDependencies env root
    let bodies := collectDefinitionBodies env [root]
    let classical := bodies.toArray.filter fun n => `Classical |>.isPrefixOf (privateToUserName n)
    unless directClassical.isEmpty && classical.isEmpty do
      throwError "Choice/Classical dependency in membership numerical body: {root}; {classical}"
    let forbidden := forbiddenNativeDependencies env nativeMembershipNumericalAllowedProjectNamespaces root
    unless forbidden.isEmpty do
      throwError "Forbidden numerical membership dependencies: {root}; {forbidden}"
    logInfo m!"Membership numerical constructor {root}: computable; no Classical body closure; \
      separate numerical allowance."

run_cmd do
  let env ← getEnv
  let graphRoots := [
    ``FailureOfComposition.NativeMembershipAssembly.acceptanceFormula,
    ``FailureOfComposition.NativeMembershipAssembly.familyAcceptance,
    ``FailureOfComposition.NativeMembershipAssembly.membershipFormula,
    ``FailureOfComposition.NativeMembershipAssembly.pointwiseGraph,
    ``FailureOfComposition.NativeMembershipAssembly.closureGraph]
  for root in graphRoots do
    let bodies := collectDefinitionBodies env [root]
    let semantic := bodies.toArray.filter fun n =>
      (`FFL.FirstOrder.Arithmetic.Bootstrapping.Derivation).isPrefixOf n ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.DerivationOf ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.Proof ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.derivation ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.derivationOf ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.proof
    unless semantic.isEmpty do
      throwError "Membership graph calls a Foundation proof predicate: {root}; {semantic}"
    logInfo m!"Structural membership graph {root}: {bodies.size} definition-body dependencies; \
      no Foundation derivation/proof predicate."
  let theoremRoots := [
    ``FailureOfComposition.NativeMembershipAssembly.acceptanceFormulaFor_eval,
    ``FailureOfComposition.NativeMembershipAssembly.acceptanceFormula_eval,
    ``FailureOfComposition.NativeMembershipAssembly.familyAcceptanceFor_eval,
    ``FailureOfComposition.NativeMembershipAssembly.familyAcceptance_eval,
    ``FailureOfComposition.NativeMembershipAssembly.membershipFormula_eval,
    ``FailureOfComposition.NativeMembershipAssembly.totality_eval,
    ``FailureOfComposition.NativeMembershipAssembly.transferBody_eval,
    ``FailureOfComposition.NativeMembershipAssembly.transferClosure_eval,
    ``FailureOfComposition.NativeMembershipAssembly.pointwiseMatrix_eval,
    ``FailureOfComposition.NativeMembershipAssembly.closureMatrix_eval,
    ``FailureOfComposition.NativeMembershipAssembly.pointwiseMatrix_valid,
    ``FailureOfComposition.NativeMembershipAssembly.closureMatrix_valid,
    ``FailureOfComposition.NativeMembershipAssembly.pointwiseSchema_provable,
    ``FailureOfComposition.NativeMembershipAssembly.closureSchema_provable,
    ``FailureOfComposition.NativeMembershipAssembly.primrec_pointwiseCtxPacked,
    ``FailureOfComposition.NativeMembershipAssembly.pointwiseGraph_iff,
    ``FailureOfComposition.NativeMembershipAssembly.pointwiseGraph_total,
    ``FailureOfComposition.NativeMembershipAssembly.pointwiseGraph_functional,
    ``FailureOfComposition.NativeMembershipAssembly.closureGraph_iff,
    ``FailureOfComposition.NativeMembershipAssembly.closureGraph_total,
    ``FailureOfComposition.NativeMembershipAssembly.closureGraph_functional,
    ``FailureOfComposition.NativeMembershipAssembly.pointwiseValue_nat,
    ``FailureOfComposition.NativeMembershipAssembly.pointwiseGraph_nat_iff,
    ``FailureOfComposition.NativeMembershipAssembly.closureValue_nat,
    ``FailureOfComposition.NativeMembershipAssembly.closureGraph_nat_iff,
    ``FailureOfComposition.NativeMembershipAssembly.primrec_closureCtxPacked,
    ``FailureOfComposition.NativeMembershipAssembly.pointwiseBody_quote,
    ``FailureOfComposition.NativeMembershipAssembly.closureBody_quote,
    ``FailureOfComposition.NativeMembershipAssembly.pointwiseSchema_quote,
    ``FailureOfComposition.NativeMembershipAssembly.closureSchema_quote,
    ``FailureOfComposition.NativeMembershipAssembly.pointwise_first,
    ``FailureOfComposition.NativeMembershipAssembly.pointwise_second,
    ``FailureOfComposition.NativeMembershipAssembly.pointwise_third,
    ``FailureOfComposition.NativeMembershipAssembly.closure_first,
    ``FailureOfComposition.NativeMembershipAssembly.closure_second,
    ``FailureOfComposition.NativeMembershipAssembly.pointwise_matrix_instance,
    ``FailureOfComposition.NativeMembershipAssembly.closure_matrix_instance,
    ``FailureOfComposition.NativeMembershipAssembly.acceptanceInstance_literal,
    ``FailureOfComposition.NativeMembershipAssembly.membershipInstance_literal,
    ``FailureOfComposition.NativeMembershipAssembly.closureInstance_literal,
    ``FailureOfComposition.NativeMembershipAssembly.acceptance_toNumVec,
    ``FailureOfComposition.NativeMembershipAssembly.membership_toNumVec,
    ``FailureOfComposition.NativeMembershipAssembly.closure_toNumVec,
    ``FailureOfComposition.NativeMembershipAssembly.derivationOf_pointwiseValue,
    ``FailureOfComposition.NativeMembershipAssembly.pointwiseGraph_preserves_derivationOf,
    ``FailureOfComposition.NativeMembershipAssembly.derivationOf_closureValue,
    ``FailureOfComposition.NativeMembershipAssembly.closureGraph_preserves_derivationOf,
    ``FailureOfComposition.NativeMembershipAssembly.proof_pointwiseValue,
    ``FailureOfComposition.NativeMembershipAssembly.proof_closureValue,
    ``FailureOfComposition.NativeMembershipAssembly.exists_standard_pointwise_seed,
    ``FailureOfComposition.NativeMembershipAssembly.exists_standard_closure_seed,
    ``FailureOfComposition.NativeMembershipAssembly.pointwiseGraph_preserves_acceptance,
    ``FailureOfComposition.NativeMembershipAssembly.closureGraph_preserves_acceptance,
    ``FailureOfComposition.NativeMembershipAssembly.exists_acceptance_proof,
    ``FailureOfComposition.NativeMembershipAssembly.exists_pointwise_assembly,
    ``FailureOfComposition.NativeMembershipAssembly.exists_closure_assembly,
    ``FailureOfComposition.NativeMembershipAssembly.exists_membership_proof,
    ``FailureOfComposition.NativeMembershipAssembly.exists_transfer_closure_proof,
    ``FailureOfComposition.NativeMembershipAssembly.exists_craig_membership_proof,
    ``FailureOfComposition.NativeMembershipAssembly.exists_craig_transfer_closure_proof,
    ``FailureOfComposition.NativeMembershipAssembly.exists_membership_proof_nat,
    ``FailureOfComposition.NativeMembershipAssembly.exists_transfer_closure_proof_nat,
    ``FailureOfComposition.NativeMembershipAssembly.exists_typed_membership_proof,
    ``FailureOfComposition.NativeMembershipAssembly.exists_typed_transfer_closure_proof,
    ``FailureOfComposition.NativeMembershipAssembly.craig_typed_membership_nat_iff]
  let arithmeticRoots := [
    ``FailureOfComposition.NativeMembershipAssembly.pointwiseMatrix_valid,
    ``FailureOfComposition.NativeMembershipAssembly.closureMatrix_valid,
    ``FailureOfComposition.NativeMembershipAssembly.pointwiseSchema_provable,
    ``FailureOfComposition.NativeMembershipAssembly.closureSchema_provable,
    ``FailureOfComposition.NativeMembershipAssembly.exists_standard_pointwise_seed,
    ``FailureOfComposition.NativeMembershipAssembly.exists_standard_closure_seed,
    ``FailureOfComposition.NativeMembershipAssembly.exists_pointwise_assembly,
    ``FailureOfComposition.NativeMembershipAssembly.exists_closure_assembly,
    ``FailureOfComposition.NativeMembershipAssembly.exists_membership_proof,
    ``FailureOfComposition.NativeMembershipAssembly.exists_transfer_closure_proof,
    ``FailureOfComposition.NativeMembershipAssembly.exists_craig_membership_proof,
    ``FailureOfComposition.NativeMembershipAssembly.exists_craig_transfer_closure_proof,
    ``FailureOfComposition.NativeMembershipAssembly.exists_membership_proof_nat,
    ``FailureOfComposition.NativeMembershipAssembly.exists_transfer_closure_proof_nat]
  let typedRoots := [
    ``FailureOfComposition.NativeMembershipAssembly.exists_typed_membership_proof,
    ``FailureOfComposition.NativeMembershipAssembly.exists_typed_transfer_closure_proof]
  for root in graphRoots ++ theoremRoots do
    let allowed := if root == ``FailureOfComposition.NativeMembershipAssembly.craig_typed_membership_nat_iff
      then nativeMembershipProductionAllowedProjectNamespaces
      else if typedRoots.contains root then nativeMembershipTypedAllowedProjectNamespaces
      else if arithmeticRoots.contains root then nativeMembershipArithmeticAllowedProjectNamespaces
      else nativeMembershipInternalAllowedProjectNamespaces
    let forbidden := forbiddenNativeDependencies env allowed root
    unless forbidden.isEmpty do
      throwError "Forbidden membership assembly dependencies: {root}; {forbidden}"
    let deps := collectDependencies env [root]
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected membership assembly axioms: {root}; {unexpected}"
    logInfo m!"Membership assembly root {root}: {deps.size} declarations; separate membership allowance; \
      no consistency or sorryAx; axioms {axioms}."

/- Numeral-arithmetic checkpoint: separate numerical/graph bodies and full
proof-and-type closures, with every preceding audit retained. -/
run_cmd do
  let env ← getEnv
  for root in [
    ``FailureOfComposition.NativeNumeralArithmetic.binaryVectorCode,
    ``FailureOfComposition.NativeNumeralArithmetic.binaryFunctionCode,
    ``FailureOfComposition.NativeNumeralArithmetic.addTermCode,
    ``FailureOfComposition.NativeNumeralArithmetic.mulTermCode,
    ``FailureOfComposition.NativeNumeralArithmetic.atomicEqCode,
    ``FailureOfComposition.NativeNumeralArithmetic.addEqCode,
    ``FailureOfComposition.NativeNumeralArithmetic.mulEqCode,
    ``FailureOfComposition.NativeNumeralArithmetic.r0BodyCode,
    ``FailureOfComposition.NativeNumeralArithmetic.reflBodyCode,
    ``FailureOfComposition.NativeNumeralArithmetic.asBodyCode,
    ``FailureOfComposition.NativeNumeralArithmetic.m0BodyCode,
    ``FailureOfComposition.NativeNumeralArithmetic.m1BodyCode,
    ``FailureOfComposition.NativeNumeralArithmetic.msBodyCode,
    ``FailureOfComposition.NativeNumeralArithmetic.nextBodyCode,
    ``FailureOfComposition.NativeNumeralArithmetic.instance3Code,
    ``FailureOfComposition.NativeNumeralArithmetic.specialize3Code,
    ``FailureOfComposition.NativeNumeralArithmetic.instance4Code,
    ``FailureOfComposition.NativeNumeralArithmetic.specialize4Code,
    ``FailureOfComposition.NativeNumeralArithmetic.addOneCode,
    ``FailureOfComposition.NativeNumeralArithmetic.addPositiveCode,
    ``FailureOfComposition.NativeNumeralArithmetic.addCtx,
    ``FailureOfComposition.NativeNumeralArithmetic.mulPositiveCode,
    ``FailureOfComposition.NativeNumeralArithmetic.mulCtx,
    ``FailureOfComposition.NativeNumeralArithmetic.addCtxPacked,
    ``FailureOfComposition.NativeNumeralArithmetic.mulCtxPacked,
    ``FailureOfComposition.NativeNumeralArithmetic.addWithSeeds,
    ``FailureOfComposition.NativeNumeralArithmetic.mulWithSeeds] do
    if isNoncomputable env root then
      throwError "Noncomputable numeral-arithmetic numerical root: {root}"
    let directClassical := directClassicalDependencies env root
    let bodies := collectDefinitionBodies env [root]
    let classical := bodies.toArray.filter fun n => `Classical |>.isPrefixOf (privateToUserName n)
    unless directClassical.isEmpty && classical.isEmpty do
      throwError "Choice/Classical in numeral-arithmetic numerical body: {root}; {classical}"
    let forbidden := forbiddenNativeDependencies env nativeNumeralNumericalAllowedProjectNamespaces root
    unless forbidden.isEmpty do
      throwError "Forbidden numeral-arithmetic numerical dependencies: {root}; {forbidden}"
    logInfo m!"Numeral numerical root {root}: computable; no Classical body closure; syntax/inference-only allowance."

run_cmd do
  let env ← getEnv
  let graphRoots := [
    ``FailureOfComposition.NativeNumeralArithmetic.addEqGraph,
    ``FailureOfComposition.NativeNumeralArithmetic.mulEqGraph,
    ``FailureOfComposition.NativeNumeralArithmetic.nextBodyGraph,
    ``FailureOfComposition.NativeNumeralArithmetic.instance3Graph,
    ``FailureOfComposition.NativeNumeralArithmetic.specialize3Graph,
    ``FailureOfComposition.NativeNumeralArithmetic.instance4Graph,
    ``FailureOfComposition.NativeNumeralArithmetic.specialize4Graph,
    ``FailureOfComposition.NativeNumeralArithmetic.addOneGraph,
    ``FailureOfComposition.NativeNumeralArithmetic.addPositiveGraph,
    ``FailureOfComposition.NativeNumeralArithmetic.AddRec.blueprint,
    ``FailureOfComposition.NativeNumeralArithmetic.addGraph,
    ``FailureOfComposition.NativeNumeralArithmetic.mulPositiveGraph,
    ``FailureOfComposition.NativeNumeralArithmetic.MulRec.blueprint,
    ``FailureOfComposition.NativeNumeralArithmetic.mulGraph]
  for root in graphRoots do
    let bodies := collectDefinitionBodies env [root]
    let semantic := bodies.toArray.filter fun n =>
      (`FFL.FirstOrder.Arithmetic.Bootstrapping.Derivation).isPrefixOf n ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.DerivationOf ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.Proof ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.derivation ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.derivationOf ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.proof
    unless semantic.isEmpty do
      throwError "Numeral-arithmetic structural graph calls a proof predicate: {root}; {semantic}"
    logInfo m!"Structural numeral graph {root}: {bodies.size} definition-body dependencies; no Foundation proof predicate."
  let theoremRoots := [
    ``FailureOfComposition.NativeNumeralArithmetic.addOneGraph_eval,
    ``FailureOfComposition.NativeNumeralArithmetic.addPositiveGraph_eval,
    ``FailureOfComposition.NativeNumeralArithmetic.addGraph_iff,
    ``FailureOfComposition.NativeNumeralArithmetic.addGraph_eval,
    ``FailureOfComposition.NativeNumeralArithmetic.addValue_defined,
    ``FailureOfComposition.NativeNumeralArithmetic.addValue_definable,
    ``FailureOfComposition.NativeNumeralArithmetic.addValue_zero,
    ``FailureOfComposition.NativeNumeralArithmetic.addValue_one,
    ``FailureOfComposition.NativeNumeralArithmetic.addValue_succ,
    ``FailureOfComposition.NativeNumeralArithmetic.addGraph_total,
    ``FailureOfComposition.NativeNumeralArithmetic.addGraph_functional,
    ``FailureOfComposition.NativeNumeralArithmetic.addOneValue_nat,
    ``FailureOfComposition.NativeNumeralArithmetic.addPositiveValue_nat,
    ``FailureOfComposition.NativeNumeralArithmetic.addValue_nat,
    ``FailureOfComposition.NativeNumeralArithmetic.addGraph_nat_iff,
    ``FailureOfComposition.NativeNumeralArithmetic.exists_standard_seeds,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec_addWithSeeds,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec_mulWithSeeds,
    ``FailureOfComposition.NativeNumeralArithmetic.standard_arithmetic_endpoint,
    ``FailureOfComposition.NativeNumeralArithmetic.addSeedValue_nat,
    ``FailureOfComposition.NativeNumeralArithmetic.mulSeedValue_nat,
    ``FailureOfComposition.NativeNumeralArithmetic.numeral_functions_nat_accepted,
    ``FailureOfComposition.NativeNumeralArithmetic.exists_standard_arithmetic_functions,
    ``FailureOfComposition.NativeNumeralArithmetic.addCtx_zero,
    ``FailureOfComposition.NativeNumeralArithmetic.addCtx_one,
    ``FailureOfComposition.NativeNumeralArithmetic.addCtx_succ,
    ``FailureOfComposition.NativeNumeralArithmetic.mulCtx_zero,
    ``FailureOfComposition.NativeNumeralArithmetic.mulCtx_one,
    ``FailureOfComposition.NativeNumeralArithmetic.mulCtx_succ,
    ``FailureOfComposition.NativeNumeralArithmetic.instance3_typed,
    ``FailureOfComposition.NativeNumeralArithmetic.derivationOf_specialize3,
    ``FailureOfComposition.NativeNumeralArithmetic.instance4_typed,
    ``FailureOfComposition.NativeNumeralArithmetic.derivationOf_specialize4,
    ``FailureOfComposition.NativeNumeralArithmetic.asBody_cast,
    ``FailureOfComposition.NativeNumeralArithmetic.msBody_cast,
    ``FailureOfComposition.NativeNumeralArithmetic.asSentence_literal,
    ``FailureOfComposition.NativeNumeralArithmetic.msSentence_literal,
    ``FailureOfComposition.NativeNumeralArithmetic.as_instance,
    ``FailureOfComposition.NativeNumeralArithmetic.ms_instance,
    ``FailureOfComposition.NativeNumeralArithmetic.r0_instance,
    ``FailureOfComposition.NativeNumeralArithmetic.refl_instance,
    ``FailureOfComposition.NativeNumeralArithmetic.m0_instance,
    ``FailureOfComposition.NativeNumeralArithmetic.m1_instance,
    ``FailureOfComposition.NativeNumeralArithmetic.z1_literal,
    ``FailureOfComposition.NativeNumeralArithmetic.as_positive_literal,
    ``FailureOfComposition.NativeNumeralArithmetic.ms_positive_literal,
    ``FailureOfComposition.NativeNumeralArithmetic.mulPositiveGraph_eval,
    ``FailureOfComposition.NativeNumeralArithmetic.mulGraph_iff,
    ``FailureOfComposition.NativeNumeralArithmetic.mulGraph_eval,
    ``FailureOfComposition.NativeNumeralArithmetic.mulValue_defined,
    ``FailureOfComposition.NativeNumeralArithmetic.mulValue_definable,
    ``FailureOfComposition.NativeNumeralArithmetic.mulValue_zero,
    ``FailureOfComposition.NativeNumeralArithmetic.mulValue_one,
    ``FailureOfComposition.NativeNumeralArithmetic.mulValue_succ,
    ``FailureOfComposition.NativeNumeralArithmetic.mulGraph_total,
    ``FailureOfComposition.NativeNumeralArithmetic.mulGraph_functional,
    ``FailureOfComposition.NativeNumeralArithmetic.mulPositiveValue_nat,
    ``FailureOfComposition.NativeNumeralArithmetic.mulValue_nat,
    ``FailureOfComposition.NativeNumeralArithmetic.mulGraph_nat_iff,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec_addOne,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec_addPositive,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec_addCtx,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec_mulPositive,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec_mulCtx,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec_addCtxPacked,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec_mulCtxPacked,
    ``FailureOfComposition.NativeNumeralArithmetic.derivationOf_addOneValue,
    ``FailureOfComposition.NativeNumeralArithmetic.derivationOf_addPositiveValue,
    ``FailureOfComposition.NativeNumeralArithmetic.derivationOf_addValue,
    ``FailureOfComposition.NativeNumeralArithmetic.derivationOf_mulPositiveValue,
    ``FailureOfComposition.NativeNumeralArithmetic.derivationOf_mulValue,
    ``FailureOfComposition.NativeNumeralArithmetic.addGraph_preserves_derivationOf,
    ``FailureOfComposition.NativeNumeralArithmetic.mulGraph_preserves_derivationOf,
    ``FailureOfComposition.NativeNumeralArithmetic.proof_addValue,
    ``FailureOfComposition.NativeNumeralArithmetic.proof_mulValue,
    ``FailureOfComposition.NativeNumeralArithmetic.accepted_iff_proof,
    ``FailureOfComposition.NativeNumeralArithmetic.addGraph_preserves_acceptance,
    ``FailureOfComposition.NativeNumeralArithmetic.mulGraph_preserves_acceptance,
    ``FailureOfComposition.NativeNumeralArithmetic.r0_provable,
    ``FailureOfComposition.NativeNumeralArithmetic.z1_provable,
    ``FailureOfComposition.NativeNumeralArithmetic.refl_provable,
    ``FailureOfComposition.NativeNumeralArithmetic.as_provable,
    ``FailureOfComposition.NativeNumeralArithmetic.m0_provable,
    ``FailureOfComposition.NativeNumeralArithmetic.m1_provable,
    ``FailureOfComposition.NativeNumeralArithmetic.ms_provable,
    ``FailureOfComposition.NativeNumeralArithmetic.bodyCode_quote,
    ``FailureOfComposition.NativeNumeralArithmetic.all_quote,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec_specialize,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec_apply,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec_nextBody,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec_instance3,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec_specialize3,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec_instance4,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec_specialize4,
    ``FailureOfComposition.NativeNumeralArithmetic.specializeCtxGraph_eval,
    ``FailureOfComposition.NativeNumeralArithmetic.applyCtxGraph_eval,
    ``FailureOfComposition.NativeNumeralArithmetic.nextBodyGraph_eval,
    ``FailureOfComposition.NativeNumeralArithmetic.instance3Graph_eval,
    ``FailureOfComposition.NativeNumeralArithmetic.specialize3Graph_eval,
    ``FailureOfComposition.NativeNumeralArithmetic.instance4Graph_eval,
    ``FailureOfComposition.NativeNumeralArithmetic.specialize4Graph_eval,
    ``FailureOfComposition.NativeNumeralArithmetic.nextBodyValue_nat,
    ``FailureOfComposition.NativeNumeralArithmetic.instance3Value_nat,
    ``FailureOfComposition.NativeNumeralArithmetic.specialize3Value_nat,
    ``FailureOfComposition.NativeNumeralArithmetic.instance4Value_nat,
    ``FailureOfComposition.NativeNumeralArithmetic.specialize4Value_nat,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec₂_binaryVectorCode,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec₂_binaryFunctionCode,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec₂_addTermCode,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec₂_mulTermCode,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec₂_atomicEqCode,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec₂_addEqCode,
    ``FailureOfComposition.NativeNumeralArithmetic.primrec₂_mulEqCode,
    ``FailureOfComposition.NativeNumeralArithmetic.addEqGraph_iff,
    ``FailureOfComposition.NativeNumeralArithmetic.mulEqGraph_iff,
    ``FailureOfComposition.NativeNumeralArithmetic.addEq_isFormula,
    ``FailureOfComposition.NativeNumeralArithmetic.mulEq_isFormula,
    ``FailureOfComposition.NativeNumeralArithmetic.addTermCode_cast,
    ``FailureOfComposition.NativeNumeralArithmetic.mulTermCode_cast,
    ``FailureOfComposition.NativeNumeralArithmetic.atomicEqCode_cast,
    ``FailureOfComposition.NativeNumeralArithmetic.addTermCode_nat,
    ``FailureOfComposition.NativeNumeralArithmetic.mulTermCode_nat,
    ``FailureOfComposition.NativeNumeralArithmetic.atomicEqCode_nat,
    ``FailureOfComposition.NativeNumeralArithmetic.addEq_nat,
    ``FailureOfComposition.NativeNumeralArithmetic.mulEq_nat,
    ``FailureOfComposition.NativeNumeralArithmetic.addTermCode_valid,
    ``FailureOfComposition.NativeNumeralArithmetic.mulTermCode_valid,
    ``FailureOfComposition.NativeNumeralArithmetic.addEqCode_encode,
    ``FailureOfComposition.NativeNumeralArithmetic.mulEqCode_encode]
  for root in graphRoots ++ theoremRoots do
    let forbidden := forbiddenNativeDependencies env nativeNumeralInternalAllowedProjectNamespaces root
    unless forbidden.isEmpty do
      throwError "Forbidden numeral-arithmetic full dependencies: {root}; {forbidden}"
    let deps := collectDependencies env [root]
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected numeral-arithmetic axioms: {root}; {unexpected}"
    logInfo m!"Numeral arithmetic root {root}: {deps.size} declarations; no production/typed/compiler allowance; axioms {axioms}."

/- Comparison roots retain the earlier audit controls. Public allowances name
individual declarations (and their generated auxiliaries); private allowances
name only the new source owners. No production, compiler, quotient, or typed
program-family namespace is added. -/
private def comparisonPublicDeclarations : Array Name := #[
    `FailureOfComposition.NativeNumeralComparison.StandardSeeds,
    `FailureOfComposition.NativeNumeralComparison.exists_standard_seeds,
    `FailureOfComposition.NativeNumeralComparison.signedEqWithSeeds,
    `FailureOfComposition.NativeNumeralComparison.primrec_signedEqWithSeeds,
    `FailureOfComposition.NativeNumeralComparison.signedLtWithSeeds,
    `FailureOfComposition.NativeNumeralComparison.primrec_signedLtWithSeeds,
    `FailureOfComposition.NativeNumeralComparison.signedEqSeedValue,
    `FailureOfComposition.NativeNumeralComparison.signedLtSeedValue,
    `FailureOfComposition.NativeNumeralComparison.standard_comparison_endpoint,
    `FailureOfComposition.NativeNumeralComparison.signedEqSeedValue_nat,
    `FailureOfComposition.NativeNumeralComparison.signedLtSeedValue_nat,
    `FailureOfComposition.NativeNumeralComparison.comparison_functions_nat_accepted,
    `FailureOfComposition.NativeNumeralComparison.exists_standard_comparison_functions,
    `FailureOfComposition.NativeNumeralComparison.Seeds8,
    `FailureOfComposition.NativeNumeralComparison.Args,
    `FailureOfComposition.NativeNumeralComparison.eqCode,
    `FailureOfComposition.NativeNumeralComparison.eqPacked,
    `FailureOfComposition.NativeNumeralComparison.ltCode,
    `FailureOfComposition.NativeNumeralComparison.ltPacked,
    `FailureOfComposition.NativeNumeralComparison.nltCode,
    `FailureOfComposition.NativeNumeralComparison.nltPacked,
    `FailureOfComposition.NativeNumeralComparison.neCode,
    `FailureOfComposition.NativeNumeralComparison.nePacked,
    `FailureOfComposition.NativeNumeralComparison.signedEqCode,
    `FailureOfComposition.NativeNumeralComparison.signedEqPacked,
    `FailureOfComposition.NativeNumeralComparison.signedLtCode,
    `FailureOfComposition.NativeNumeralComparison.signedLtPacked,
    `FailureOfComposition.NativeNumeralComparison.primrec_eqCode,
    `FailureOfComposition.NativeNumeralComparison.primrec_eqPacked,
    `FailureOfComposition.NativeNumeralComparison.primrec_ltCode,
    `FailureOfComposition.NativeNumeralComparison.primrec_ltPacked,
    `FailureOfComposition.NativeNumeralComparison.primrec_nltCode,
    `FailureOfComposition.NativeNumeralComparison.primrec_nltPacked,
    `FailureOfComposition.NativeNumeralComparison.primrec_neCode,
    `FailureOfComposition.NativeNumeralComparison.primrec_nePacked,
    `FailureOfComposition.NativeNumeralComparison.primrec_signedEqCode,
    `FailureOfComposition.NativeNumeralComparison.primrec_signedEqPacked,
    `FailureOfComposition.NativeNumeralComparison.primrec_signedLtCode,
    `FailureOfComposition.NativeNumeralComparison.primrec_signedLtPacked,
    `FailureOfComposition.NativeNumeralComparison.eqGraph,
    `FailureOfComposition.NativeNumeralComparison.ltGraph,
    `FailureOfComposition.NativeNumeralComparison.nltGraph,
    `FailureOfComposition.NativeNumeralComparison.neGraph,
    `FailureOfComposition.NativeNumeralComparison.signedEqGraph,
    `FailureOfComposition.NativeNumeralComparison.signedLtGraph,
    `FailureOfComposition.NativeNumeralComparison.eqValue,
    `FailureOfComposition.NativeNumeralComparison.eqGraph_eval,
    `FailureOfComposition.NativeNumeralComparison.eqGraph_iff,
    `FailureOfComposition.NativeNumeralComparison.eqGraph_total,
    `FailureOfComposition.NativeNumeralComparison.eqGraph_functional,
    `FailureOfComposition.NativeNumeralComparison.ltValue,
    `FailureOfComposition.NativeNumeralComparison.ltGraph_eval,
    `FailureOfComposition.NativeNumeralComparison.ltGraph_iff,
    `FailureOfComposition.NativeNumeralComparison.ltGraph_total,
    `FailureOfComposition.NativeNumeralComparison.ltGraph_functional,
    `FailureOfComposition.NativeNumeralComparison.nltValue,
    `FailureOfComposition.NativeNumeralComparison.nltGraph_eval,
    `FailureOfComposition.NativeNumeralComparison.nltGraph_iff,
    `FailureOfComposition.NativeNumeralComparison.nltGraph_total,
    `FailureOfComposition.NativeNumeralComparison.nltGraph_functional,
    `FailureOfComposition.NativeNumeralComparison.neValue,
    `FailureOfComposition.NativeNumeralComparison.neGraph_eval,
    `FailureOfComposition.NativeNumeralComparison.neGraph_iff,
    `FailureOfComposition.NativeNumeralComparison.neGraph_total,
    `FailureOfComposition.NativeNumeralComparison.neGraph_functional,
    `FailureOfComposition.NativeNumeralComparison.signedEqValue,
    `FailureOfComposition.NativeNumeralComparison.signedEqGraph_eval,
    `FailureOfComposition.NativeNumeralComparison.signedEqGraph_iff,
    `FailureOfComposition.NativeNumeralComparison.signedEqGraph_total,
    `FailureOfComposition.NativeNumeralComparison.signedEqGraph_functional,
    `FailureOfComposition.NativeNumeralComparison.signedLtValue,
    `FailureOfComposition.NativeNumeralComparison.signedLtGraph_eval,
    `FailureOfComposition.NativeNumeralComparison.signedLtGraph_iff,
    `FailureOfComposition.NativeNumeralComparison.signedLtGraph_total,
    `FailureOfComposition.NativeNumeralComparison.signedLtGraph_functional,
    `FailureOfComposition.NativeNumeralComparison.signedEqValue_of_eq,
    `FailureOfComposition.NativeNumeralComparison.signedEqValue_of_ne,
    `FailureOfComposition.NativeNumeralComparison.signedLtValue_of_lt,
    `FailureOfComposition.NativeNumeralComparison.signedLtValue_of_nlt,
    `FailureOfComposition.NativeNumeralComparison.sub_nat,
    `FailureOfComposition.NativeNumeralComparison.modelSub_nat,
    `FailureOfComposition.NativeNumeralComparison.eqValue_nat,
    `FailureOfComposition.NativeNumeralComparison.eqGraph_nat_iff,
    `FailureOfComposition.NativeNumeralComparison.ltValue_nat,
    `FailureOfComposition.NativeNumeralComparison.ltGraph_nat_iff,
    `FailureOfComposition.NativeNumeralComparison.nltValue_nat,
    `FailureOfComposition.NativeNumeralComparison.nltGraph_nat_iff,
    `FailureOfComposition.NativeNumeralComparison.neValue_nat,
    `FailureOfComposition.NativeNumeralComparison.neGraph_nat_iff,
    `FailureOfComposition.NativeNumeralComparison.signedEqValue_nat,
    `FailureOfComposition.NativeNumeralComparison.signedEqGraph_nat_iff,
    `FailureOfComposition.NativeNumeralComparison.signedLtValue_nat,
    `FailureOfComposition.NativeNumeralComparison.signedLtGraph_nat_iff,
    `FailureOfComposition.NativeNumeralComparison.instance2Code,
    `FailureOfComposition.NativeNumeralComparison.specialize2Code,
    `FailureOfComposition.NativeNumeralComparison.primrec_instance2,
    `FailureOfComposition.NativeNumeralComparison.primrec_specialize2,
    `FailureOfComposition.NativeNumeralComparison.instance2Graph,
    `FailureOfComposition.NativeNumeralComparison.specialize2Graph,
    `FailureOfComposition.NativeNumeralComparison.instance2Value,
    `FailureOfComposition.NativeNumeralComparison.specialize2Value,
    `FailureOfComposition.NativeNumeralComparison.instance2Graph_eval,
    `FailureOfComposition.NativeNumeralComparison.specialize2Graph_eval,
    `FailureOfComposition.NativeNumeralComparison.instance2_typed,
    `FailureOfComposition.NativeNumeralComparison.derivationOf_specialize2,
    `FailureOfComposition.NativeNumeralComparison.ltBridgeBody_cast,
    `FailureOfComposition.NativeNumeralComparison.ltBridgeSentence_literal,
    `FailureOfComposition.NativeNumeralComparison.nltBridgeBody_cast,
    `FailureOfComposition.NativeNumeralComparison.nltBridgeSentence_literal,
    `FailureOfComposition.NativeNumeralComparison.neForwardBody_cast,
    `FailureOfComposition.NativeNumeralComparison.neForwardSentence_literal,
    `FailureOfComposition.NativeNumeralComparison.neReverseBody_cast,
    `FailureOfComposition.NativeNumeralComparison.neReverseSentence_literal,
    `FailureOfComposition.NativeNumeralComparison.ltBridge_instance,
    `FailureOfComposition.NativeNumeralComparison.nltBridge_instance,
    `FailureOfComposition.NativeNumeralComparison.neForward_instance,
    `FailureOfComposition.NativeNumeralComparison.neReverse_instance,
    `FailureOfComposition.NativeNumeralComparison.instance2Value_nat,
    `FailureOfComposition.NativeNumeralComparison.specialize2Value_nat,
    `FailureOfComposition.NativeNumeralComparison.SeedsIn,
    `FailureOfComposition.NativeNumeralComparison.lt_difference,
    `FailureOfComposition.NativeNumeralComparison.nlt_difference,
    `FailureOfComposition.NativeNumeralComparison.ltBridge_literal,
    `FailureOfComposition.NativeNumeralComparison.nltBridge_literal,
    `FailureOfComposition.NativeNumeralComparison.derivationOf_eqValue,
    `FailureOfComposition.NativeNumeralComparison.derivationOf_ltValue,
    `FailureOfComposition.NativeNumeralComparison.derivationOf_nltValue,
    `FailureOfComposition.NativeNumeralComparison.derivationOf_neValue,
    `FailureOfComposition.NativeNumeralComparison.derivationOf_signedEqValue,
    `FailureOfComposition.NativeNumeralComparison.derivationOf_signedLtValue,
    `FailureOfComposition.NativeNumeralComparison.eqGraph_preserves_derivationOf,
    `FailureOfComposition.NativeNumeralComparison.ltGraph_preserves_derivationOf,
    `FailureOfComposition.NativeNumeralComparison.nltGraph_preserves_derivationOf,
    `FailureOfComposition.NativeNumeralComparison.neGraph_preserves_derivationOf,
    `FailureOfComposition.NativeNumeralComparison.signedEqGraph_preserves_derivationOf,
    `FailureOfComposition.NativeNumeralComparison.signedLtGraph_preserves_derivationOf,
    `FailureOfComposition.NativeNumeralComparison.derivationOf_lt_zero_one,
    `FailureOfComposition.NativeNumeralComparison.derivationOf_nlt_self,
    `FailureOfComposition.NativeNumeralComparison.derivationOf_nlt_zero_zero,
    `FailureOfComposition.NativeNumeralComparison.signed_comparisons_singleton,
    `FailureOfComposition.NativeNumeralComparison.SeedProofs,
    `FailureOfComposition.NativeNumeralComparison.SeedProofs.toSeedsIn,
    `FailureOfComposition.NativeNumeralComparison.proof_eqValue,
    `FailureOfComposition.NativeNumeralComparison.eqValue_accepted,
    `FailureOfComposition.NativeNumeralComparison.eqGraph_preserves_acceptance,
    `FailureOfComposition.NativeNumeralComparison.proof_ltValue,
    `FailureOfComposition.NativeNumeralComparison.ltValue_accepted,
    `FailureOfComposition.NativeNumeralComparison.ltGraph_preserves_acceptance,
    `FailureOfComposition.NativeNumeralComparison.proof_nltValue,
    `FailureOfComposition.NativeNumeralComparison.nltValue_accepted,
    `FailureOfComposition.NativeNumeralComparison.nltGraph_preserves_acceptance,
    `FailureOfComposition.NativeNumeralComparison.proof_neValue,
    `FailureOfComposition.NativeNumeralComparison.neValue_accepted,
    `FailureOfComposition.NativeNumeralComparison.neGraph_preserves_acceptance,
    `FailureOfComposition.NativeNumeralComparison.proof_signedEqValue,
    `FailureOfComposition.NativeNumeralComparison.signedEqValue_accepted,
    `FailureOfComposition.NativeNumeralComparison.signedEqGraph_preserves_acceptance,
    `FailureOfComposition.NativeNumeralComparison.proof_signedLtValue,
    `FailureOfComposition.NativeNumeralComparison.signedLtValue_accepted,
    `FailureOfComposition.NativeNumeralComparison.signedLtGraph_preserves_acceptance,
    `FailureOfComposition.NativeNumeralComparison.ltBridgeMatrix,
    `FailureOfComposition.NativeNumeralComparison.ltBridgeBody,
    `FailureOfComposition.NativeNumeralComparison.ltBridgeSentence,
    `FailureOfComposition.NativeNumeralComparison.nltBridgeMatrix,
    `FailureOfComposition.NativeNumeralComparison.nltBridgeBody,
    `FailureOfComposition.NativeNumeralComparison.nltBridgeSentence,
    `FailureOfComposition.NativeNumeralComparison.neForwardMatrix,
    `FailureOfComposition.NativeNumeralComparison.neForwardBody,
    `FailureOfComposition.NativeNumeralComparison.neForwardSentence,
    `FailureOfComposition.NativeNumeralComparison.neReverseMatrix,
    `FailureOfComposition.NativeNumeralComparison.neReverseBody,
    `FailureOfComposition.NativeNumeralComparison.neReverseSentence,
    `FailureOfComposition.NativeNumeralComparison.ltBridgeBodyCode,
    `FailureOfComposition.NativeNumeralComparison.nltBridgeBodyCode,
    `FailureOfComposition.NativeNumeralComparison.neForwardBodyCode,
    `FailureOfComposition.NativeNumeralComparison.neReverseBodyCode,
    `FailureOfComposition.NativeNumeralComparison.ltBridge_provable,
    `FailureOfComposition.NativeNumeralComparison.nltBridge_provable,
    `FailureOfComposition.NativeNumeralComparison.neForward_provable,
    `FailureOfComposition.NativeNumeralComparison.neReverse_provable,
    `FailureOfComposition.NativeNumeralComparison.relationCode,
    `FailureOfComposition.NativeNumeralComparison.primrec₂_relationCode,
    `FailureOfComposition.NativeNumeralComparison.eqTargetCode,
    `FailureOfComposition.NativeNumeralComparison.primrec₂_eqTargetCode,
    `FailureOfComposition.NativeNumeralComparison.neTargetCode,
    `FailureOfComposition.NativeNumeralComparison.primrec₂_neTargetCode,
    `FailureOfComposition.NativeNumeralComparison.ltTargetCode,
    `FailureOfComposition.NativeNumeralComparison.primrec₂_ltTargetCode,
    `FailureOfComposition.NativeNumeralComparison.nltTargetCode,
    `FailureOfComposition.NativeNumeralComparison.primrec₂_nltTargetCode,
    `FailureOfComposition.NativeNumeralComparison.signedEqTargetCode,
    `FailureOfComposition.NativeNumeralComparison.signedLtTargetCode,
    `FailureOfComposition.NativeNumeralComparison.primrec₂_signedEqTargetCode,
    `FailureOfComposition.NativeNumeralComparison.primrec₂_signedLtTargetCode,
    `FailureOfComposition.NativeNumeralComparison.eqTarget,
    `FailureOfComposition.NativeNumeralComparison.eqTargetGraph,
    `FailureOfComposition.NativeNumeralComparison.eqTargetGraph_eval,
    `FailureOfComposition.NativeNumeralComparison.eqTarget_isFormula,
    `FailureOfComposition.NativeNumeralComparison.relationCode_eq_cast,
    `FailureOfComposition.NativeNumeralComparison.neTarget,
    `FailureOfComposition.NativeNumeralComparison.neTargetGraph,
    `FailureOfComposition.NativeNumeralComparison.neTargetGraph_eval,
    `FailureOfComposition.NativeNumeralComparison.neTarget_isFormula,
    `FailureOfComposition.NativeNumeralComparison.relationCode_ne_cast,
    `FailureOfComposition.NativeNumeralComparison.ltTarget,
    `FailureOfComposition.NativeNumeralComparison.ltTargetGraph,
    `FailureOfComposition.NativeNumeralComparison.ltTargetGraph_eval,
    `FailureOfComposition.NativeNumeralComparison.ltTarget_isFormula,
    `FailureOfComposition.NativeNumeralComparison.relationCode_lt_cast,
    `FailureOfComposition.NativeNumeralComparison.nltTarget,
    `FailureOfComposition.NativeNumeralComparison.nltTargetGraph,
    `FailureOfComposition.NativeNumeralComparison.nltTargetGraph_eval,
    `FailureOfComposition.NativeNumeralComparison.nltTarget_isFormula,
    `FailureOfComposition.NativeNumeralComparison.relationCode_nlt_cast,
    `FailureOfComposition.NativeNumeralComparison.signedEqTarget,
    `FailureOfComposition.NativeNumeralComparison.signedLtTarget,
    `FailureOfComposition.NativeNumeralComparison.signedEqTargetGraph,
    `FailureOfComposition.NativeNumeralComparison.signedLtTargetGraph,
    `FailureOfComposition.NativeNumeralComparison.signedEqTargetGraph_eval,
    `FailureOfComposition.NativeNumeralComparison.signedLtTargetGraph_eval,
    `FailureOfComposition.NativeNumeralComparison.signedEqTarget_isFormula,
    `FailureOfComposition.NativeNumeralComparison.signedLtTarget_isFormula,
    `FailureOfComposition.NativeNumeralComparison.neg_eqTarget,
    `FailureOfComposition.NativeNumeralComparison.neg_ltTarget,
    `FailureOfComposition.NativeNumeralComparison.eqTargetGraph_total,
    `FailureOfComposition.NativeNumeralComparison.eqTargetGraph_functional,
    `FailureOfComposition.NativeNumeralComparison.neTargetGraph_total,
    `FailureOfComposition.NativeNumeralComparison.neTargetGraph_functional,
    `FailureOfComposition.NativeNumeralComparison.ltTargetGraph_total,
    `FailureOfComposition.NativeNumeralComparison.ltTargetGraph_functional,
    `FailureOfComposition.NativeNumeralComparison.nltTargetGraph_total,
    `FailureOfComposition.NativeNumeralComparison.nltTargetGraph_functional,
    `FailureOfComposition.NativeNumeralComparison.signedEqTargetGraph_total,
    `FailureOfComposition.NativeNumeralComparison.signedEqTargetGraph_functional,
    `FailureOfComposition.NativeNumeralComparison.signedLtTargetGraph_total,
    `FailureOfComposition.NativeNumeralComparison.signedLtTargetGraph_functional,
    `FailureOfComposition.NativeNumeralComparison.eqTarget_nat,
    `FailureOfComposition.NativeNumeralComparison.neTarget_nat,
    `FailureOfComposition.NativeNumeralComparison.ltTarget_nat,
    `FailureOfComposition.NativeNumeralComparison.nltTarget_nat,
    `FailureOfComposition.NativeNumeralComparison.signedEqTarget_nat,
    `FailureOfComposition.NativeNumeralComparison.signedLtTarget_nat,
    `FailureOfComposition.NativeNumeralComparison.eqTargetCode_encode,
    `FailureOfComposition.NativeNumeralComparison.neTargetCode_encode,
    `FailureOfComposition.NativeNumeralComparison.ltTargetCode_encode,
    `FailureOfComposition.NativeNumeralComparison.nltTargetCode_encode,
    `FailureOfComposition.NativeNumeralComparison.eqTargetGraph_nat_iff,
    `FailureOfComposition.NativeNumeralComparison.neTargetGraph_nat_iff,
    `FailureOfComposition.NativeNumeralComparison.ltTargetGraph_nat_iff,
    `FailureOfComposition.NativeNumeralComparison.nltTargetGraph_nat_iff,
    `FailureOfComposition.NativeNumeralComparison.signedEqTargetGraph_nat_iff,
    `FailureOfComposition.NativeNumeralComparison.signedLtTargetGraph_nat_iff,
    `FailureOfComposition.NativeNumeralComparison.signedEqSentence,
    `FailureOfComposition.NativeNumeralComparison.signedLtSentence,
    `FailureOfComposition.NativeNumeralComparison.signedEqSentence_encode,
    `FailureOfComposition.NativeNumeralComparison.signedLtSentence_encode,
    `FailureOfComposition.NativeNumeralComparison.typed_signed_comparisons,
    `FailureOfComposition.NativeNumeralComparison.craig_signedEq_adequacy,
    `FailureOfComposition.NativeNumeralComparison.craig_signedLt_adequacy,
    `FailureOfComposition.NativeNumeralComparison.craig_signed_comparisons
  ]

private def comparisonNumericalAllowed : Array Name :=
  nativeNumeralNumericalAllowedProjectNamespaces ++ comparisonPublicDeclarations ++ #[
    `FailureOfComposition.NativeNumeralComparisonConstructor,
    `FailureOfComposition.NativeNumeralComparisonInstances,
    `FailureOfComposition.NativeNumeralComparisonSeeds,
    `FailureOfComposition.NativeNumeralComparisonSyntax
  ]

private def comparisonInternalAllowed : Array Name :=
  nativeNumeralInternalAllowedProjectNamespaces ++ comparisonPublicDeclarations ++ #[
    `FailureOfComposition.NativeNumeralComparisonApplications,
    `FailureOfComposition.NativeNumeralComparisonConstructor,
    `FailureOfComposition.NativeNumeralComparisonGraph,
    `FailureOfComposition.NativeNumeralComparisonInstances,
    `FailureOfComposition.NativeNumeralComparisonPreservation,
    `FailureOfComposition.NativeNumeralComparisonProof,
    `FailureOfComposition.NativeNumeralComparisonSeeds,
    `FailureOfComposition.NativeNumeralComparisonSyntax,
    `FailureOfComposition.NativeNumeralComparisonTypedApplications
  ]

run_cmd do
  let env ← getEnv
  for root in [
    ``FailureOfComposition.NativeNumeralComparison.signedEqWithSeeds,
    ``FailureOfComposition.NativeNumeralComparison.signedLtWithSeeds,
    ``FailureOfComposition.NativeNumeralComparison.eqCode,
    ``FailureOfComposition.NativeNumeralComparison.eqPacked,
    ``FailureOfComposition.NativeNumeralComparison.ltCode,
    ``FailureOfComposition.NativeNumeralComparison.ltPacked,
    ``FailureOfComposition.NativeNumeralComparison.nltCode,
    ``FailureOfComposition.NativeNumeralComparison.nltPacked,
    ``FailureOfComposition.NativeNumeralComparison.neCode,
    ``FailureOfComposition.NativeNumeralComparison.nePacked,
    ``FailureOfComposition.NativeNumeralComparison.signedEqCode,
    ``FailureOfComposition.NativeNumeralComparison.signedEqPacked,
    ``FailureOfComposition.NativeNumeralComparison.signedLtCode,
    ``FailureOfComposition.NativeNumeralComparison.signedLtPacked,
    ``FailureOfComposition.NativeNumeralComparison.instance2Code,
    ``FailureOfComposition.NativeNumeralComparison.specialize2Code,
    ``FailureOfComposition.NativeNumeralComparison.ltBridgeBodyCode,
    ``FailureOfComposition.NativeNumeralComparison.nltBridgeBodyCode,
    ``FailureOfComposition.NativeNumeralComparison.neForwardBodyCode,
    ``FailureOfComposition.NativeNumeralComparison.neReverseBodyCode,
    ``FailureOfComposition.NativeNumeralComparison.relationCode,
    ``FailureOfComposition.NativeNumeralComparison.eqTargetCode,
    ``FailureOfComposition.NativeNumeralComparison.neTargetCode,
    ``FailureOfComposition.NativeNumeralComparison.ltTargetCode,
    ``FailureOfComposition.NativeNumeralComparison.nltTargetCode,
    ``FailureOfComposition.NativeNumeralComparison.signedEqTargetCode,
    ``FailureOfComposition.NativeNumeralComparison.signedLtTargetCode] do
    if isNoncomputable env root then
      throwError "Noncomputable comparison numerical root: {root}"
    let bodies := collectDefinitionBodies env [root]
    let classical := bodies.toArray.filter fun n => `Classical |>.isPrefixOf (privateToUserName n)
    unless (directClassicalDependencies env root).isEmpty && classical.isEmpty do
      throwError "Classical comparison numerical body: {root}; {classical}"
    let forbidden := forbiddenNativeDependencies env comparisonNumericalAllowed root
    unless forbidden.isEmpty do
      throwError "Forbidden comparison numerical closure: {root}; {forbidden}"
    logInfo m!"Comparison numerical root {root}: computable, Classical-free body, restricted closure."

run_cmd do
  let env ← getEnv
  let structuralRoots := [
    ``FailureOfComposition.NativeNumeralComparison.signedEqSeedValue,
    ``FailureOfComposition.NativeNumeralComparison.signedLtSeedValue,
    ``FailureOfComposition.NativeNumeralComparison.eqGraph,
    ``FailureOfComposition.NativeNumeralComparison.ltGraph,
    ``FailureOfComposition.NativeNumeralComparison.nltGraph,
    ``FailureOfComposition.NativeNumeralComparison.neGraph,
    ``FailureOfComposition.NativeNumeralComparison.signedEqGraph,
    ``FailureOfComposition.NativeNumeralComparison.signedLtGraph,
    ``FailureOfComposition.NativeNumeralComparison.eqValue,
    ``FailureOfComposition.NativeNumeralComparison.ltValue,
    ``FailureOfComposition.NativeNumeralComparison.nltValue,
    ``FailureOfComposition.NativeNumeralComparison.neValue,
    ``FailureOfComposition.NativeNumeralComparison.signedEqValue,
    ``FailureOfComposition.NativeNumeralComparison.signedLtValue,
    ``FailureOfComposition.NativeNumeralComparison.instance2Graph,
    ``FailureOfComposition.NativeNumeralComparison.specialize2Graph,
    ``FailureOfComposition.NativeNumeralComparison.instance2Value,
    ``FailureOfComposition.NativeNumeralComparison.specialize2Value,
    ``FailureOfComposition.NativeNumeralComparison.eqTarget,
    ``FailureOfComposition.NativeNumeralComparison.eqTargetGraph,
    ``FailureOfComposition.NativeNumeralComparison.neTarget,
    ``FailureOfComposition.NativeNumeralComparison.neTargetGraph,
    ``FailureOfComposition.NativeNumeralComparison.ltTarget,
    ``FailureOfComposition.NativeNumeralComparison.ltTargetGraph,
    ``FailureOfComposition.NativeNumeralComparison.nltTarget,
    ``FailureOfComposition.NativeNumeralComparison.nltTargetGraph,
    ``FailureOfComposition.NativeNumeralComparison.signedEqTarget,
    ``FailureOfComposition.NativeNumeralComparison.signedLtTarget,
    ``FailureOfComposition.NativeNumeralComparison.signedEqTargetGraph,
    ``FailureOfComposition.NativeNumeralComparison.signedLtTargetGraph]
  for root in structuralRoots do
    let bodies := collectDefinitionBodies env [root]
    let semantic := bodies.toArray.filter fun n =>
      (`FFL.FirstOrder.Arithmetic.Bootstrapping.Derivation).isPrefixOf n ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.DerivationOf ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.Proof ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.derivation ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.derivationOf ||
      n == ``FFL.FirstOrder.Arithmetic.Bootstrapping.proof ||
      (privateToUserName n).toString.endsWith "exists_standard_seed" ||
      n == ``FailureOfComposition.NativeNumeralComparison.exists_standard_seeds
    unless semantic.isEmpty do
      throwError "Comparison structural body calls proof selection/predicate: {root}; {semantic}"
    logInfo m!"Comparison structural root {root}: {bodies.size} body dependencies, no proof selection."
  let theoremRoots := [
    ``FailureOfComposition.NativeNumeralComparison.exists_standard_seeds,
    ``FailureOfComposition.NativeNumeralComparison.primrec_signedEqWithSeeds,
    ``FailureOfComposition.NativeNumeralComparison.primrec_signedLtWithSeeds,
    ``FailureOfComposition.NativeNumeralComparison.standard_comparison_endpoint,
    ``FailureOfComposition.NativeNumeralComparison.signedEqSeedValue_nat,
    ``FailureOfComposition.NativeNumeralComparison.signedLtSeedValue_nat,
    ``FailureOfComposition.NativeNumeralComparison.comparison_functions_nat_accepted,
    ``FailureOfComposition.NativeNumeralComparison.exists_standard_comparison_functions,
    ``FailureOfComposition.NativeNumeralComparison.primrec_eqCode,
    ``FailureOfComposition.NativeNumeralComparison.primrec_eqPacked,
    ``FailureOfComposition.NativeNumeralComparison.primrec_ltCode,
    ``FailureOfComposition.NativeNumeralComparison.primrec_ltPacked,
    ``FailureOfComposition.NativeNumeralComparison.primrec_nltCode,
    ``FailureOfComposition.NativeNumeralComparison.primrec_nltPacked,
    ``FailureOfComposition.NativeNumeralComparison.primrec_neCode,
    ``FailureOfComposition.NativeNumeralComparison.primrec_nePacked,
    ``FailureOfComposition.NativeNumeralComparison.primrec_signedEqCode,
    ``FailureOfComposition.NativeNumeralComparison.primrec_signedEqPacked,
    ``FailureOfComposition.NativeNumeralComparison.primrec_signedLtCode,
    ``FailureOfComposition.NativeNumeralComparison.primrec_signedLtPacked,
    ``FailureOfComposition.NativeNumeralComparison.eqGraph_eval,
    ``FailureOfComposition.NativeNumeralComparison.eqGraph_iff,
    ``FailureOfComposition.NativeNumeralComparison.eqGraph_total,
    ``FailureOfComposition.NativeNumeralComparison.eqGraph_functional,
    ``FailureOfComposition.NativeNumeralComparison.ltGraph_eval,
    ``FailureOfComposition.NativeNumeralComparison.ltGraph_iff,
    ``FailureOfComposition.NativeNumeralComparison.ltGraph_total,
    ``FailureOfComposition.NativeNumeralComparison.ltGraph_functional,
    ``FailureOfComposition.NativeNumeralComparison.nltGraph_eval,
    ``FailureOfComposition.NativeNumeralComparison.nltGraph_iff,
    ``FailureOfComposition.NativeNumeralComparison.nltGraph_total,
    ``FailureOfComposition.NativeNumeralComparison.nltGraph_functional,
    ``FailureOfComposition.NativeNumeralComparison.neGraph_eval,
    ``FailureOfComposition.NativeNumeralComparison.neGraph_iff,
    ``FailureOfComposition.NativeNumeralComparison.neGraph_total,
    ``FailureOfComposition.NativeNumeralComparison.neGraph_functional,
    ``FailureOfComposition.NativeNumeralComparison.signedEqGraph_eval,
    ``FailureOfComposition.NativeNumeralComparison.signedEqGraph_iff,
    ``FailureOfComposition.NativeNumeralComparison.signedEqGraph_total,
    ``FailureOfComposition.NativeNumeralComparison.signedEqGraph_functional,
    ``FailureOfComposition.NativeNumeralComparison.signedLtGraph_eval,
    ``FailureOfComposition.NativeNumeralComparison.signedLtGraph_iff,
    ``FailureOfComposition.NativeNumeralComparison.signedLtGraph_total,
    ``FailureOfComposition.NativeNumeralComparison.signedLtGraph_functional,
    ``FailureOfComposition.NativeNumeralComparison.signedEqValue_of_eq,
    ``FailureOfComposition.NativeNumeralComparison.signedEqValue_of_ne,
    ``FailureOfComposition.NativeNumeralComparison.signedLtValue_of_lt,
    ``FailureOfComposition.NativeNumeralComparison.signedLtValue_of_nlt,
    ``FailureOfComposition.NativeNumeralComparison.sub_nat,
    ``FailureOfComposition.NativeNumeralComparison.modelSub_nat,
    ``FailureOfComposition.NativeNumeralComparison.eqValue_nat,
    ``FailureOfComposition.NativeNumeralComparison.eqGraph_nat_iff,
    ``FailureOfComposition.NativeNumeralComparison.ltValue_nat,
    ``FailureOfComposition.NativeNumeralComparison.ltGraph_nat_iff,
    ``FailureOfComposition.NativeNumeralComparison.nltValue_nat,
    ``FailureOfComposition.NativeNumeralComparison.nltGraph_nat_iff,
    ``FailureOfComposition.NativeNumeralComparison.neValue_nat,
    ``FailureOfComposition.NativeNumeralComparison.neGraph_nat_iff,
    ``FailureOfComposition.NativeNumeralComparison.signedEqValue_nat,
    ``FailureOfComposition.NativeNumeralComparison.signedEqGraph_nat_iff,
    ``FailureOfComposition.NativeNumeralComparison.signedLtValue_nat,
    ``FailureOfComposition.NativeNumeralComparison.signedLtGraph_nat_iff,
    ``FailureOfComposition.NativeNumeralComparison.primrec_instance2,
    ``FailureOfComposition.NativeNumeralComparison.primrec_specialize2,
    ``FailureOfComposition.NativeNumeralComparison.instance2Graph_eval,
    ``FailureOfComposition.NativeNumeralComparison.specialize2Graph_eval,
    ``FailureOfComposition.NativeNumeralComparison.instance2_typed,
    ``FailureOfComposition.NativeNumeralComparison.derivationOf_specialize2,
    ``FailureOfComposition.NativeNumeralComparison.ltBridgeBody_cast,
    ``FailureOfComposition.NativeNumeralComparison.ltBridgeSentence_literal,
    ``FailureOfComposition.NativeNumeralComparison.nltBridgeBody_cast,
    ``FailureOfComposition.NativeNumeralComparison.nltBridgeSentence_literal,
    ``FailureOfComposition.NativeNumeralComparison.neForwardBody_cast,
    ``FailureOfComposition.NativeNumeralComparison.neForwardSentence_literal,
    ``FailureOfComposition.NativeNumeralComparison.neReverseBody_cast,
    ``FailureOfComposition.NativeNumeralComparison.neReverseSentence_literal,
    ``FailureOfComposition.NativeNumeralComparison.ltBridge_instance,
    ``FailureOfComposition.NativeNumeralComparison.nltBridge_instance,
    ``FailureOfComposition.NativeNumeralComparison.neForward_instance,
    ``FailureOfComposition.NativeNumeralComparison.neReverse_instance,
    ``FailureOfComposition.NativeNumeralComparison.instance2Value_nat,
    ``FailureOfComposition.NativeNumeralComparison.specialize2Value_nat,
    ``FailureOfComposition.NativeNumeralComparison.lt_difference,
    ``FailureOfComposition.NativeNumeralComparison.nlt_difference,
    ``FailureOfComposition.NativeNumeralComparison.ltBridge_literal,
    ``FailureOfComposition.NativeNumeralComparison.nltBridge_literal,
    ``FailureOfComposition.NativeNumeralComparison.derivationOf_eqValue,
    ``FailureOfComposition.NativeNumeralComparison.derivationOf_ltValue,
    ``FailureOfComposition.NativeNumeralComparison.derivationOf_nltValue,
    ``FailureOfComposition.NativeNumeralComparison.derivationOf_neValue,
    ``FailureOfComposition.NativeNumeralComparison.derivationOf_signedEqValue,
    ``FailureOfComposition.NativeNumeralComparison.derivationOf_signedLtValue,
    ``FailureOfComposition.NativeNumeralComparison.eqGraph_preserves_derivationOf,
    ``FailureOfComposition.NativeNumeralComparison.ltGraph_preserves_derivationOf,
    ``FailureOfComposition.NativeNumeralComparison.nltGraph_preserves_derivationOf,
    ``FailureOfComposition.NativeNumeralComparison.neGraph_preserves_derivationOf,
    ``FailureOfComposition.NativeNumeralComparison.signedEqGraph_preserves_derivationOf,
    ``FailureOfComposition.NativeNumeralComparison.signedLtGraph_preserves_derivationOf,
    ``FailureOfComposition.NativeNumeralComparison.derivationOf_lt_zero_one,
    ``FailureOfComposition.NativeNumeralComparison.derivationOf_nlt_self,
    ``FailureOfComposition.NativeNumeralComparison.derivationOf_nlt_zero_zero,
    ``FailureOfComposition.NativeNumeralComparison.signed_comparisons_singleton,
    ``FailureOfComposition.NativeNumeralComparison.SeedProofs.toSeedsIn,
    ``FailureOfComposition.NativeNumeralComparison.proof_eqValue,
    ``FailureOfComposition.NativeNumeralComparison.eqValue_accepted,
    ``FailureOfComposition.NativeNumeralComparison.eqGraph_preserves_acceptance,
    ``FailureOfComposition.NativeNumeralComparison.proof_ltValue,
    ``FailureOfComposition.NativeNumeralComparison.ltValue_accepted,
    ``FailureOfComposition.NativeNumeralComparison.ltGraph_preserves_acceptance,
    ``FailureOfComposition.NativeNumeralComparison.proof_nltValue,
    ``FailureOfComposition.NativeNumeralComparison.nltValue_accepted,
    ``FailureOfComposition.NativeNumeralComparison.nltGraph_preserves_acceptance,
    ``FailureOfComposition.NativeNumeralComparison.proof_neValue,
    ``FailureOfComposition.NativeNumeralComparison.neValue_accepted,
    ``FailureOfComposition.NativeNumeralComparison.neGraph_preserves_acceptance,
    ``FailureOfComposition.NativeNumeralComparison.proof_signedEqValue,
    ``FailureOfComposition.NativeNumeralComparison.signedEqValue_accepted,
    ``FailureOfComposition.NativeNumeralComparison.signedEqGraph_preserves_acceptance,
    ``FailureOfComposition.NativeNumeralComparison.proof_signedLtValue,
    ``FailureOfComposition.NativeNumeralComparison.signedLtValue_accepted,
    ``FailureOfComposition.NativeNumeralComparison.signedLtGraph_preserves_acceptance,
    ``FailureOfComposition.NativeNumeralComparison.ltBridge_provable,
    ``FailureOfComposition.NativeNumeralComparison.nltBridge_provable,
    ``FailureOfComposition.NativeNumeralComparison.neForward_provable,
    ``FailureOfComposition.NativeNumeralComparison.neReverse_provable,
    ``FailureOfComposition.NativeNumeralComparison.primrec₂_relationCode,
    ``FailureOfComposition.NativeNumeralComparison.primrec₂_eqTargetCode,
    ``FailureOfComposition.NativeNumeralComparison.primrec₂_neTargetCode,
    ``FailureOfComposition.NativeNumeralComparison.primrec₂_ltTargetCode,
    ``FailureOfComposition.NativeNumeralComparison.primrec₂_nltTargetCode,
    ``FailureOfComposition.NativeNumeralComparison.primrec₂_signedEqTargetCode,
    ``FailureOfComposition.NativeNumeralComparison.primrec₂_signedLtTargetCode,
    ``FailureOfComposition.NativeNumeralComparison.eqTargetGraph_eval,
    ``FailureOfComposition.NativeNumeralComparison.eqTarget_isFormula,
    ``FailureOfComposition.NativeNumeralComparison.relationCode_eq_cast,
    ``FailureOfComposition.NativeNumeralComparison.neTargetGraph_eval,
    ``FailureOfComposition.NativeNumeralComparison.neTarget_isFormula,
    ``FailureOfComposition.NativeNumeralComparison.relationCode_ne_cast,
    ``FailureOfComposition.NativeNumeralComparison.ltTargetGraph_eval,
    ``FailureOfComposition.NativeNumeralComparison.ltTarget_isFormula,
    ``FailureOfComposition.NativeNumeralComparison.relationCode_lt_cast,
    ``FailureOfComposition.NativeNumeralComparison.nltTargetGraph_eval,
    ``FailureOfComposition.NativeNumeralComparison.nltTarget_isFormula,
    ``FailureOfComposition.NativeNumeralComparison.relationCode_nlt_cast,
    ``FailureOfComposition.NativeNumeralComparison.signedEqTargetGraph_eval,
    ``FailureOfComposition.NativeNumeralComparison.signedLtTargetGraph_eval,
    ``FailureOfComposition.NativeNumeralComparison.signedEqTarget_isFormula,
    ``FailureOfComposition.NativeNumeralComparison.signedLtTarget_isFormula,
    ``FailureOfComposition.NativeNumeralComparison.neg_eqTarget,
    ``FailureOfComposition.NativeNumeralComparison.neg_ltTarget,
    ``FailureOfComposition.NativeNumeralComparison.eqTargetGraph_total,
    ``FailureOfComposition.NativeNumeralComparison.eqTargetGraph_functional,
    ``FailureOfComposition.NativeNumeralComparison.neTargetGraph_total,
    ``FailureOfComposition.NativeNumeralComparison.neTargetGraph_functional,
    ``FailureOfComposition.NativeNumeralComparison.ltTargetGraph_total,
    ``FailureOfComposition.NativeNumeralComparison.ltTargetGraph_functional,
    ``FailureOfComposition.NativeNumeralComparison.nltTargetGraph_total,
    ``FailureOfComposition.NativeNumeralComparison.nltTargetGraph_functional,
    ``FailureOfComposition.NativeNumeralComparison.signedEqTargetGraph_total,
    ``FailureOfComposition.NativeNumeralComparison.signedEqTargetGraph_functional,
    ``FailureOfComposition.NativeNumeralComparison.signedLtTargetGraph_total,
    ``FailureOfComposition.NativeNumeralComparison.signedLtTargetGraph_functional,
    ``FailureOfComposition.NativeNumeralComparison.eqTarget_nat,
    ``FailureOfComposition.NativeNumeralComparison.neTarget_nat,
    ``FailureOfComposition.NativeNumeralComparison.ltTarget_nat,
    ``FailureOfComposition.NativeNumeralComparison.nltTarget_nat,
    ``FailureOfComposition.NativeNumeralComparison.signedEqTarget_nat,
    ``FailureOfComposition.NativeNumeralComparison.signedLtTarget_nat,
    ``FailureOfComposition.NativeNumeralComparison.eqTargetCode_encode,
    ``FailureOfComposition.NativeNumeralComparison.neTargetCode_encode,
    ``FailureOfComposition.NativeNumeralComparison.ltTargetCode_encode,
    ``FailureOfComposition.NativeNumeralComparison.nltTargetCode_encode,
    ``FailureOfComposition.NativeNumeralComparison.eqTargetGraph_nat_iff,
    ``FailureOfComposition.NativeNumeralComparison.neTargetGraph_nat_iff,
    ``FailureOfComposition.NativeNumeralComparison.ltTargetGraph_nat_iff,
    ``FailureOfComposition.NativeNumeralComparison.nltTargetGraph_nat_iff,
    ``FailureOfComposition.NativeNumeralComparison.signedEqTargetGraph_nat_iff,
    ``FailureOfComposition.NativeNumeralComparison.signedLtTargetGraph_nat_iff,
    ``FailureOfComposition.NativeNumeralComparison.signedEqSentence_encode,
    ``FailureOfComposition.NativeNumeralComparison.signedLtSentence_encode,
    ``FailureOfComposition.NativeNumeralComparison.typed_signed_comparisons,
    ``FailureOfComposition.NativeNumeralComparison.craig_signedEq_adequacy,
    ``FailureOfComposition.NativeNumeralComparison.craig_signedLt_adequacy,
    ``FailureOfComposition.NativeNumeralComparison.craig_signed_comparisons]
  for root in structuralRoots ++ theoremRoots do
    let forbidden := forbiddenNativeDependencies env comparisonInternalAllowed root
    unless forbidden.isEmpty do
      throwError "Forbidden comparison full closure: {root}; {forbidden}"
    let deps := collectDependencies env [root]
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected comparison axioms: {root}; {unexpected}"
    logInfo m!"Comparison full root {root}: {deps.size} declarations; axioms {axioms}."


run_cmd do
  let env ← getEnv
  let core := [
    ``FailureOfComposition.ProductionStageClosure.proof_T_equality_stage_bound,
    ``FailureOfComposition.ProductionStageClosure.transport_implies_stage_bound,
    ``FailureOfComposition.ProductionStageClosure.findStage_spec,
    ``FailureOfComposition.ProductionStageClosure.primrec_findStage,
    ``FailureOfComposition.ProductionStageClosure.primrec_transportWithBound,
    ``FailureOfComposition.ProductionStageClosure.transportWithBound_correct,
    ``FailureOfComposition.ProductionStageClosure.has_transport_iff_stage_bound,
    ``FailureOfComposition.ProductionStageClosure.no_transport_of_no_stage_bound,
    ``FailureOfComposition.StageEnumerationObstruction.primrec_delayedStage,
    ``FailureOfComposition.StageEnumerationObstruction.delayedStage_bound,
    ``FailureOfComposition.StageEnumerationObstruction.exists_delayedStage,
    ``FailureOfComposition.StageEnumerationObstruction.no_primrec_stage_bound,
    ``FailureOfComposition.StageEnumerationObstruction.no_primrec_stage_selector]
  let comparison := [
    ``FailureOfComposition.ProductionRepairClosure.repair_backtranslation_implies_transport,
    ``FailureOfComposition.ProductionRepairClosure.repair_backtranslation_implies_stage_bound,
    ``FailureOfComposition.ProductionRepairClosure.no_repair_backtranslation_of_no_stage_bound]
  for root in core ++ comparison do
    let deps := collectDependencies env [root]
    let forbidden := deps.toArray.filter fun n =>
      n == ``sorryAx || hasForbiddenConsistencyBaseName n ||
      (`FailureOfComposition.GeneratedCongruence).isPrefixOf (privateToUserName n) ||
      n == ``FailureOfComposition.ProgramIndices.PointwiseIndex ||
      n == ``FailureOfComposition.ConcreteIndices.PointwiseIndex ||
      (core.contains root &&
        (`FailureOfComposition.PrfEqTransportRepair).isPrefixOf (nativeClassificationName env n))
    unless forbidden.isEmpty do
      throwError "Forbidden production-stage dependency: {root}; {forbidden}"
    let axioms := deps.toArray.filter fun n =>
      match env.checked.get.find? n with
      | some (.axiomInfo _) => true
      | _ => false
    let unexpected := axioms.filter fun n =>
      n != ``propext && n != ``Classical.choice && n != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "Unexpected production-stage axiom: {root}; {unexpected}"
    logInfo m!"Production stage root {root}: original-checker boundary; axioms {axioms}."
  for root in [
    ``FailureOfComposition.ProductionStageClosure.findStage,
    ``FailureOfComposition.ProductionStageClosure.transportWithBound,
    ``FailureOfComposition.StageEnumerationObstruction.delayedStage] do
    if isNoncomputable env root then
      throwError "Noncomputable stage operation: {root}"
    let bodies := collectDefinitionBodies env [root]
    let forbidden := bodies.toArray.filter fun n =>
      (`Classical).isPrefixOf (privateToUserName n) ||
      (`FailureOfComposition.PrfEqTransportRepair).isPrefixOf (nativeClassificationName env n)
    unless forbidden.isEmpty do
      throwError "Forbidden stage-operation body: {root}; {forbidden}"
    logInfo m!"Production stage operation {root}: computable, Classical-free definition body."
