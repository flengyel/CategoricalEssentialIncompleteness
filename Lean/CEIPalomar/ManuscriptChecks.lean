module

public import CEIPalomar.Solution
import all CEIPalomar.Solution
import all CEIPalomar.CalculusDefinitions
public import CategoricalEssentialIncompleteness.V46RestrictionSubobjectInseparability
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! # Corollary 4.8 in the total category -/

@[expose] public section
noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CEIPalomar.ManuscriptChecks

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

example {V X : D} (P : Calculus X) (hP : IsNullaryCalculus V P) (a b : Subobject X)
    (hab : a ⊓ b = ⊥) (hc : P.consistent (P.signedTheory a b)) :
    P.essentiallyIncomplete (P.signedTheory a b) ↔ inseparable a b :=
  CEIPalomar.essential_incomplete_iff_inseparable P hP a b hab hc

example {V X : D} (P : Calculus X) (hP : IsNullaryCalculus V P)
    (d : X ⟶ (⊤_ D) ⨿ (⊤_ D)) :
    ∃ T : Subobject P.sentence, P.generated T = T ∧ P.consistent T ∧ P.complete T ∧
      ∀ a b : Subobject X, a.arrow ≫ d = terminal.from (a : D) ≫ coprod.inr →
        b.arrow ≫ d = terminal.from (b : D) ≫ coprod.inl → P.signedTheory a b ≤ T :=
  CEIPalomar.boolean_assignment P hP d

/-- First-order syntax with propositional atoms specified by each object `Y` and initial
derivation algebras for all axiom subobjects give `IsNullaryCalculus` at `X`. -/
theorem isNullaryCalculus_of_data {V : D}
    (syntaxData : (Y : D) → CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => Y) 0)
    (proofs : (Y : D) → (A : Subobject (syntaxData Y).sentenceObject) →
      Endofunctor.Algebra ((syntaxData Y).logicalRules A.arrow).inference)
    (initial : ∀ Y A, IsInitial (proofs Y A)) (X : D) :
    IsNullaryCalculus V (ofNullaryPresentation ⟨syntaxData, proofs, initial⟩ X) :=
  ⟨⟨syntaxData, proofs, initial⟩, rfl⟩

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]
variable [Splits C] [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C]
variable [Regular (RestrictionSubobjects.Tot C)] [FinitaryExtensive (RestrictionSubobjects.Tot C)]

/-- For a disjoint pair with consistent signed theory, essential incompleteness
is equivalent to inseparability of the corresponding restriction idempotents. -/
theorem essentiallyIncomplete_iff_inseparable_domains
    (inverses : RestrictionSubobjects.MonoInverses C)
    {V X : RestrictionSubobjects.Tot C} (F : NullaryPresentations V)
    (a b : Subobject X) (hab : a ⊓ b = ⊥)
    (hc : (F.presentation X).Consistent (SignedFirstOrder.theory F a b).val) :
    (F.presentation X).EssentiallyIncomplete (SignedFirstOrder.theory F a b) ↔
      LocalConnectedness.Inseparable (RestrictionSubobjects.domain inverses a)
        (RestrictionSubobjects.domain inverses b) := by
  have hP := isNullaryCalculus_of_data F.syntaxData F.proofs F.initial X
  calc
    _ ↔ _ := (essentiallyIncomplete_signedTheory_iff F a b).symm
    _ ↔ inseparable a b :=
      CEIPalomar.essential_incomplete_iff_inseparable (ofNullaryPresentation F X) hP a b hab hc
    _ ↔ SubobjectInseparable a b := (subobjectInseparable_iff_inseparable a b).symm
    _ ↔ _ := (RestrictionSubobjects.inseparable_iff inverses a b).symm

@[inherit_doc essentiallyIncomplete_iff_inseparable_domains]
alias printed_corollary := essentiallyIncomplete_iff_inseparable_domains

/-- If complementary subobjects separate `a` and `b`, the signed theory of
`a` and `b` has a closed, consistent, complete extension. -/
theorem complete_extension_of_separator {V X : D} (F : NullaryPresentations V)
    (a b : Subobject X) (hs : HasSubobjectSeparator a b) :
    ∃ U : (F.presentation X).Theories, (SignedFirstOrder.theory F a b).val ≤ U.val ∧
      (F.presentation X).Consistent U.val ∧ (F.presentation X).Complete U.val := by
  obtain ⟨d, ha, hb⟩ := (subobject_separator_iff_boolean a b).mp hs
  have hP := isNullaryCalculus_of_data F.syntaxData F.proofs F.initial X
  obtain ⟨T, closed, consistent, complete, extendsPair⟩ := CEIPalomar.boolean_assignment
    (ofNullaryPresentation F X) hP d
  exact ⟨⟨T, closed⟩, extendsPair a b ha hb, consistent, complete⟩

example : ∃ (D : Type) (cat : Category.{0} D), letI := cat
    ∃ (reg : Regular D) (ext : FinitaryExtensive D), letI := reg; letI := ext
      ∃ (V X : D) (P : Calculus X) (a b : Subobject X),
        IsNullaryCalculus V P ∧ inseparable a b ∧
          P.essentiallyIncomplete (P.signedTheory a b) :=
  CEIPalomar.exists_inseparable_example

end CEIPalomar.ManuscriptChecks

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let corollary ← getConstInfo
    ``CEIPalomar.ManuscriptChecks.essentiallyIncomplete_iff_inseparable_domains
  let some proof := corollary.value? (allowOpaque := true) | throwError "Recovery proof missing"
  for needed in #[``CEIPalomar.essential_incomplete_iff_inseparable,
      ``RestrictionSubobjects.inseparable_iff] do
    unless proof.getUsedConstants.contains needed do
      throwError "The restriction-idempotent equivalence must use {needed}"
  let packageModules := #[`CEIPalomar.CalculusDefinitions, `CEIPalomar.Solution]
  let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let inSolution := (env.getModuleIdxFor? name).any fun idx =>
      packageModules.contains (env.header.moduleNames.getD idx.toNat .anonymous)
    if inSolution || Name.isPrefixOf `CEIPalomar.ManuscriptChecks name then
      let axioms ← collectAxioms name
      unless axioms.all allowed.contains do
        throwError "Unexpected axioms for {name}: {axioms}"
      checked := checked + 1
  logInfo m!"Checked transitive axioms of {checked} package and recovery declarations."
