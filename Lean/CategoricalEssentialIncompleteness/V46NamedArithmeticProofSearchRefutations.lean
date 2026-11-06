/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearch
import CategoricalEssentialIncompleteness.V46SyntacticGeneratedRefutations

/-! # The actual theorem/refutation image predicates in the partial lift -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.CoprodStruct
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch

open NamedArithmeticSignature

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem positive_theorem_image (Γ : Carrier) (φ : Formula) (n : M) :
    (positive Γ φ).val.Evalb ![n] ↔
      (SyntacticGeneratedAxioms.theoremCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
          ![NamedArithmeticFixedSubstitution.value φ n] :=
  (positive_eval M Γ φ n).trans
    (SyntacticGeneratedAxioms.literalTheoremCarrier_model 𝗣𝗔
      variableSymbols functionSymbols relationSymbols bound M Γ _)

/-- The sentence guard is a theorem of the constructed fixed-formula map,
not an additional assumption on its values. -/
theorem negative_literal_refutation (Γ : Carrier) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : M) :
    (negative Γ φ).val.Evalb ![n] ↔
      (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
          ![NamedArithmeticFixedSubstitution.value φ n] := by
  rw [SyntacticGeneratedAxioms.literalRefutationCarrier_eval 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound M Γ _]
  exact (negative_eval M Γ φ n).trans
    ⟨fun h => ⟨NamedArithmeticFixedSubstitution.value_sentence (M := M) φ hφ n,h⟩,
      fun h => h.2⟩

theorem negative_refutation_image (Γ : Carrier) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : M) :
    (negative Γ φ).val.Evalb ![n] ↔
      (SyntacticGeneratedAxioms.refutationCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
          ![NamedArithmeticFixedSubstitution.value φ n] :=
  (negative_literal_refutation M Γ φ hφ n).trans
    (SyntacticGeneratedAxioms.refutationCarrier_literal 𝗣𝗔
      variableSymbols functionSymbols relationSymbols bound M Γ _).symm

/-- Both fibers are identified with the actual constructed Γ images. The
only condition is their disjointness in the particular interpreting model. -/
theorem image_fibers (Γ : Carrier) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (hd : ∀ n : M, ¬(
      (SyntacticGeneratedAxioms.theoremCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
          ![NamedArithmeticFixedSubstitution.value φ n] ∧
      (SyntacticGeneratedAxioms.refutationCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
          ![NamedArithmeticFixedSubstitution.value φ n])) :
    Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map (ell Γ φ))
      (summand0 (PartialFun.of M) (PartialFun.of M)) =
        setIdem {n : M | (SyntacticGeneratedAxioms.refutationCarrier 𝗣𝗔
          variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
            ![NamedArithmeticFixedSubstitution.value φ n]} ∧
    Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map (ell Γ φ))
      (summand1 (PartialFun.of M) (PartialFun.of M)) =
        setIdem {n : M | (SyntacticGeneratedAxioms.theoremCarrier 𝗣𝗔
          variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
            ![NamedArithmeticFixedSubstitution.value φ n]} := by
  have hdisjoint : ∀ n : M, ¬((positive Γ φ).val.Evalb ![n] ∧ (negative Γ φ).val.Evalb ![n]) := by
    intro n hn
    exact hd n ⟨(positive_theorem_image M Γ φ n).mp hn.1,
      (negative_refutation_image M Γ φ hφ n).mp hn.2⟩
  constructor
  · simpa only [negative_refutation_image M Γ φ hφ] using pull_summand0 M Γ φ hdisjoint
  · simpa only [positive_theorem_image M Γ φ] using pull_summand1 M Γ φ hdisjoint

end Models

/-- The model-independent source lift for the actual generated theory,
with both of the manuscript's reversed theorem/refutation fibers. -/
theorem actual_partial_proof_search (Γ : Carrier) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    ∃ l : omegaObject 𝗣𝗔 ⟶ coprod (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔),
      ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔],
        (∀ n : M, ¬(
          (SyntacticGeneratedAxioms.theoremCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
              ![NamedArithmeticFixedSubstitution.value φ n] ∧
          (SyntacticGeneratedAxioms.refutationCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
              ![NamedArithmeticFixedSubstitution.value φ n])) →
        Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map l)
          (summand0 (PartialFun.of M) (PartialFun.of M)) =
            setIdem {n : M | (SyntacticGeneratedAxioms.refutationCarrier 𝗣𝗔
              variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
                ![NamedArithmeticFixedSubstitution.value φ n]} ∧
        Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 M).map l)
          (summand1 (PartialFun.of M) (PartialFun.of M)) =
            setIdem {n : M | (SyntacticGeneratedAxioms.theoremCarrier 𝗣𝗔
              variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
                ![NamedArithmeticFixedSubstitution.value φ n]} := by
  exact ⟨ell Γ φ,fun M _ _ hd => image_fibers M Γ φ hφ hd⟩

end CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch
