module

import CategoricalEssentialIncompleteness.V46TuringObjectRecognition
import CategoricalEssentialIncompleteness.V46SliceUnitFactorization
import CategoricalEssentialIncompleteness.V46JaniczakSignedTheory
import CategoricalEssentialIncompleteness.V46ArithmeticUniformIndependent
import CategoricalEssentialIncompleteness.V46MillerFixedPoint
import CategoricalEssentialIncompleteness.V46ForkTupleTuringParameters
import CategoricalEssentialIncompleteness.V46MachineOracleTuring
import CategoricalEssentialIncompleteness.V46SyntacticNonLocalConnectedness

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

-- This uses both directions of recognition with the totality precisely on the section.
universe u v
section
open PCategoryStruct RecursionCategory
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
example (U X Y : C) (eval : nearProd U U ⟶ U) (he : IsTuringMorphism eval)
    (retracts : ∀ T : C, ∃ (j : T ⟶ U) (r : U ⟶ T), isTotal j ∧ j ≫ r = 𝟙 T) :
    ∃ f : nearProd U X ⟶ Y, IsTuringMorphism f :=
  (turingObject_iff U).mpr ⟨⟨eval,he⟩,retracts⟩ X Y
end

section
open FFL FFL.FirstOrder Janiczak
example {P N : Set ℕ} (dis : Disjoint P N) (hp : REPred (· ∈ P)) (hn : REPred (· ∈ N))
    (inseparable : Numerical.RecursivelyInseparable P N) (U : Theory FOL.L)
    (extendsSigned : FOL.theory (Signed P N) ⊆ U) (consistent : Entailment.Consistent U) :
    Entailment.Consistent (FOL.theory (Signed P N)) ∧
      ¬ ComputablePred (fun w : ℕ ↦ ∃ φ : Sentence FOL.L, Encodable.encode φ = w ∧ U ⊢ φ) := by
  obtain ⟨base, _, _, equivalence⟩ := FOL.signed_janiczak dis hp hn
  exact ⟨base, equivalence.mpr inseparable U extendsSigned consistent⟩

example {P N C : Set ℕ} (hp : P ⊆ C) (hn : Disjoint C N) (decides : ComputablePred (· ∈ C)) :
    ∃ U : Theory FOL.L, FOL.theory (Signed P N) ⊆ U ∧ Entailment.Consistent U ∧
      ComputablePred (fun w : ℕ ↦ ∃ φ : Sentence FOL.L, Encodable.encode φ = w ∧ U ⊢ φ) :=
  FOL.decidable_native_extension hp hn decides
end

section
open Miller
example : ∃ a : Point, ∀ d (r : Set.Icc (0 : ℝ) 1),
    (∀ p ∈ representations a, ∀ k : ℕ, ∃ i : ℕ, i ∈ OracleProgram.numberedEval d p k ∧
       |(Rationals.q i : ℝ) - (r : ℝ)| < ((2 : ℝ)^k)⁻¹) → a d = r := by
  obtain ⟨a, uniqueCoordinate⟩ := exists_isMiller
  exact ⟨a,uniqueCoordinate⟩
end

section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic NamedArithmeticSignature
example : ∃ q : ArithmeticIndexedAxioms.parameter ⟶ ArithmeticIndexedAxioms.sentence,
    ∀ e : ℕ, Entailment.Consistent (ArithmeticNamedProofConnectives.system
      (ArithmeticUniformIndependent.gamma e)) → ∃ φ : Formula,
      formulaCode φ = ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map q
        (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ e)).val.val ∧
      ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (ArithmeticUniformIndependent.gamma e) φ ∧
      ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (ArithmeticUniformIndependent.gamma e) (.neg φ) := by
  obtain ⟨q,h⟩ := ArithmeticUniformIndependent.uniform_independent_sentences
  refine ⟨q, ?_⟩
  intro e hcons
  obtain ⟨φ, _, val, pos, neg⟩ := h e hcons
  exact ⟨φ,val,pos,neg⟩
end

section
open ForkTupleEvaluation
example {Y : ForkSpans} (f : forkProduct Y universal ⟶ universal) :
    ∃ c : Y ⟶ universal, isTotal c ∧ forkProducts.map c (𝟙 universal) ≫ tau = f :=
  ⟨forkParameter f, forkParameter_total f, fork_parameterizes f⟩
end

-- Completeness at a consistent base precludes an assignment at the index of the empty extension.
example {Sentence : Type} (neg : Sentence → Sentence) (proves : Sentence → Prop)
    (complete : ∀ p, proves p ∨ proves (neg p)) :
    ¬ ∃ p, ¬ proves p ∧ ¬ proves (neg p) := by
  rintro ⟨p,hp,hn⟩
  exact (complete p).elim hp hn

#check @CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted.machine_no_lift
#check @CategoricalEssentialIncompleteness.V46.PartialSliceChangeBase.right_unit_total_iff
