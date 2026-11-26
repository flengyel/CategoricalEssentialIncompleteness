module

import CategoricalEssentialIncompleteness.V46JaniczakSignedTheory
import CategoricalEssentialIncompleteness.V46DiscreteTuringInseparability
import CategoricalEssentialIncompleteness.V46TrivialDominicalCategory
import CategoricalEssentialIncompleteness.V46SyntheticIndependence
import CategoricalEssentialIncompleteness.V46EssentialUndecidability
import CategoricalEssentialIncompleteness.V46RelationalSignatureAdjunction
import CategoricalEssentialIncompleteness.V46MillerFixedPoint
import CategoricalEssentialIncompleteness.V46MillerCutReduction
import CategoricalEssentialIncompleteness.V46MillerIncompleteness
import CategoricalEssentialIncompleteness.V46MillerUnanimity
import CategoricalEssentialIncompleteness.V46ArithmeticUniformIndependent
import CategoricalEssentialIncompleteness.V46ForkFirstOrderApplication
import CategoricalEssentialIncompleteness.V46SyntacticNonLocalConnectedness
import CategoricalEssentialIncompleteness.V46MachineOracleTuring
import CategoricalEssentialIncompleteness.V46EffectiveExtensibility
import CategoricalEssentialIncompleteness.V46InferenceChecks

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46
open FFL FFL.FirstOrder

namespace FirstReader81

/-- Existence and the single machine for unanimity hold simultaneously for an actual sequence. -/
theorem miller_with_machine : ∃ a : ℕ → Set.Icc (0 : ℝ) 1,
    (∀ (e : ℕ) (r : Set.Icc (0 : ℝ) 1), (∀ p, Miller.rho p = a → ∀ k : ℕ, ∃ j : ℕ,
       j ∈ Miller.OracleProgram.numberedEval e p k ∧ |(Miller.Rationals.q j : ℝ) - (r : ℝ)| < ((2 : ℝ)^k)⁻¹) → a e = r) ∧
    ∃ c, ∀ p, Miller.rho p = a → ∀ e n m : ℕ,
      m ∈ Miller.OracleProgram.numberedEval c p (Nat.pair e n) ↔
        ∀ q, Miller.rho q = a → m ∈ Miller.OracleProgram.numberedEval e q n := by
  obtain ⟨a, h⟩ := Miller.exists_isMiller
  exact ⟨a,h,Miller.Unanimity.unanimityIndex,fun p hp e n m ↦
    Miller.Unanimity.unanimityIndex_graph a p hp e n m⟩

/-- The actual theory of equivalence relations excludes a recursive separator, for every
    native consistent extension and its actual Gödel codes. -/
theorem class_sizes (P N : Set ℕ) (disj : Disjoint P N) :
    (∀ U : Theory Janiczak.FOL.L, Janiczak.FOL.theory (Janiczak.Signed P N) ⊆ U →
       Entailment.Consistent U → ¬ ComputablePred (fun w : ℕ ↦
         ∃ φ : Sentence Janiczak.FOL.L, Encodable.encode φ = w ∧ U ⊢ φ)) ↔
    ¬ ∃ D : Set ℕ, ComputablePred (· ∈ D) ∧ P ⊆ D ∧ Disjoint D N := by
  exact (Janiczak.FOL.signed_essentiallyUndecidable_iff disj).trans (and_iff_right disj)

/-- A native provability-code decider in a consistent extension would separate the reduced pair. -/
theorem visser (L : Language) [Encodable (Sentence L)] (P N : Set ℕ)
    (T U : Theory L) (f : ℕ → Sentence L) (inc : T ⊆ U) (hU : Entailment.Consistent U)
    (h : CategoricalEssentialIncompleteness.Numerical.RecursivelyInseparable P N)
    (hc : Computable (fun n ↦ Encodable.encode (f n)))
    (pos : ∀ n ∈ P, T ⊢ f n) (neg : ∀ n ∈ N, T ⊢ ∼(f n)) :
    ¬ ComputablePred (fun w : ℕ ↦ ∃ φ : Sentence L, Encodable.encode φ = w ∧ U ⊢ φ) :=
  essentiallyUndecidable_of_recursiveReduction T h f hc pos neg U
    (Theory.Proof.weakerThan_of_le inc) hU

/-- A concrete diagonal index supplies the independent sentence of the given extension. -/
theorem synthetic (S : Type) (neg : S → S)
    (θ : ℕ → SyntheticComputability.PartialFunction ℕ ℕ)
    (hen : SyntheticComputability.Enumerates θ)
    (T U : SyntheticComputability.FormalSystem S neg) (inc : ∀ φ, T.provable φ → U.provable φ)
    (r : ℕ → S) (hp : ∀ n, (θ n).Converges n 1 → T.provable (r n))
    (hn : ∀ n, (θ n).Converges n 0 → T.provable (neg (r n))) :
    ∃ p : S, ¬ U.provable p ∧ ¬ U.provable (neg p) := by
  obtain ⟨n,h⟩ := SyntheticComputability.independent_in_extension θ hen T r hp hn U inc
  exact ⟨r n,h⟩

universe u
/-- Formula-valued interpretations of every generator in its own finite context. -/
noncomputable def interpretations (A : Voutsadakis.HSet.{u}) (Z : Voutsadakis.Signature.{u}) :
    (Voutsadakis.freeSignature.obj A ⟶ Z) ≃ A.Components (Voutsadakis.Formula.hierarchy Z.symbols) :=
  (Voutsadakis.signatureAdjunction.homEquiv A Z).trans (Voutsadakis.HSet.homEquivComponents _ _)

open CategoryTheory.PCategoryStruct CategoryTheory.CoprodStruct
open TrivialDominicalCategory in
/-- Sections, distributivity and a Turing morphism can hold while its two diagonal domains are separable. -/
theorem zero_object_diagonal : DiPaolaHeller.IsTuringMorphism evaluator ∧
    ¬ Inseparable (Idem.pull (diag One.obj ≫ evaluator) (summand0 One.obj One.obj))
      (Idem.pull (diag One.obj ≫ evaluator) (summand1 One.obj One.obj)) :=
  ⟨evaluator_turing, diagonal_pair_separated⟩

open FailureOfComposition FailureOfComposition.TypedProgramCategory FFL.FirstOrder.Arithmetic
open SyntacticPredicates ConnectedNumeralDomains in
/-- The unprimed source fails to be locally connected for the specified consistent c.e. extension. -/
theorem unprimed (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Entailment.Consistent T] [T.RE] :
    ¬ LocallyConnected (PrintedObjectCoding.NormalizedCategory T) := unprimed_not_locallyConnected T

open OracleComputation OracleComputation.Restricted in
/-- A single ordinary recursive specialization of the machine-domain index works for every oracle. -/
theorem domain_specialization : ∃ σ : ℕ → ℕ → ℕ, Computable₂ σ ∧ ∀ A e z x,
    (Miller.OracleProgram.numberedEval (σ e z) (bits A) x).Dom ↔
    (Miller.OracleProgram.numberedEval e (bits A) (Nat.pair z x)).Dom :=
  ⟨sectionIndex, sectionIndex_computable, machine_section⟩

open Miller in
/-- The same actual sequence has the two-sided recursive cut reduction and the native
    finite-proof independence assertion for every uniformly enumerable extension. -/
theorem cuts_and_field : ∃ a : Miller.Point,
    (∃ h : ℕ → ℕ, Computable h ∧
      h ⁻¹' CutDigits.lowerCut a = {e | ∃ m, m ∈ Unanimity.tau a e e ∧ m%2=0} ∧
      h ⁻¹' CutDigits.upperCut a = {e | ∃ m, m ∈ Unanimity.tau a e e ∧ m%2=1}) ∧
    ∀ Γ : Set ℕ, Uniform.Enumerable (Uniform.Family.ofPoint a) (· ∈ Γ) →
      RealClosedBounds.Extends a Γ → TheoryDomainApplication.Consistent Γ →
      ∃ φ : OrderedFieldSyntax.Formula, φ.freeVariables = [] ∧
        ¬ RealClosedBounds.Proof Γ φ ∧ ¬ RealClosedBounds.Proof Γ (.neg φ) := by
  obtain ⟨a,h⟩ := exists_isMiller
  exact ⟨a,Cut.printed_cut_reduction a h,Incompleteness.native_incomplete a h⟩

open FFL.FirstOrder.Arithmetic NamedArithmeticSignature in
/-- Both signs of the actual output of a single total PA morphism are excluded. -/
theorem one_arithmetic_morphism :
    ∃ q : ArithmeticIndexedAxioms.parameter ⟶ ArithmeticIndexedAxioms.sentence,
      ∀ e : ℕ, Entailment.Consistent (ArithmeticNamedProofConnectives.system
        (ArithmeticIndexedAxioms.fiberAxioms ArithmeticIndexedPAEnumeration.axiomCodes e)) →
        ∃ φ : NamedArithmeticSignature.Formula,
          φ.freeVariables = [] ∧ formulaCode φ =
            ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map q
              (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ e)).val.val ∧
          ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound
            (ArithmeticUniformIndependent.gamma e) φ ∧
          ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound
            (ArithmeticUniformIndependent.gamma e) (.neg φ) :=
  ArithmeticUniformIndependent.uniform_independent_sentences

open ForkEndpointSentences NumericalTuples in
/-- Independently choose the vertex and the external c.e. axiom set on that vertex. -/
theorem each_endpoint (i : Bool) (A : Set (Tuple (carrier i).dimension)) (hA : REPred (· ∈ A))
    (ext : theorems i ⊆ ForkFirstOrderApplication.closureSet i A hA)
    (con : ∀ x ∈ ForkFirstOrderApplication.closureSet i A hA,
       (neg i).toFun x ∉ ForkFirstOrderApplication.closureSet i A hA) :
    ∃ x : NumericalTuples.Point (carrier i), x ∉ ForkFirstOrderApplication.closureSet i A hA ∧
      (neg i).toFun x ∉ ForkFirstOrderApplication.closureSet i A hA :=
  ForkFirstOrderApplication.printed_statement.2.2.2 i A hA ext con

end FirstReader81

#check @CategoricalEssentialIncompleteness.V46.ProgramOrder.exists_inseparable
#check @CategoricalEssentialIncompleteness.V46.ProgramOrder.terminal_predicate_of_coded_order
#check @CategoricalEssentialIncompleteness.V46.EffectiveExtensibility.exists_complete_presentation_without_extender
#check @CategoricalEssentialIncompleteness.V46.least_closed_image
#check @CategoricalEssentialIncompleteness.V46.RulePresentation.least_theorem_subobject
#check @CategoricalEssentialIncompleteness.V46.ArithmeticUniformIndependent.uniform_independent_sentences
#check @CategoricalEssentialIncompleteness.V46.ForkFirstOrderApplication.printed_statement
#print axioms FirstReader81.miller_with_machine
#print axioms FirstReader81.class_sizes
#print axioms FirstReader81.visser
#print axioms FirstReader81.synthetic
#print axioms FirstReader81.interpretations
#print axioms FirstReader81.zero_object_diagonal
#print axioms FirstReader81.unprimed
#print axioms FirstReader81.domain_specialization

#print axioms FirstReader81.cuts_and_field
#print axioms FirstReader81.one_arithmetic_morphism
#print axioms FirstReader81.each_endpoint
