/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalBoundsModels
import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalBoundsUltrapower
import CategoricalEssentialIncompleteness.V46ArithmeticNamedAxiomComparison

/-! # Diagonal bounds from derivability of the actual named PA axioms

The extension hypothesis is the native PA arithmetic/order and induction
scheme with finite universal closure. Its comparison with source PA
axioms is a proved theorem, not an additional premise of these results.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds

open NamedArithmeticSignature

theorem standard_sentences (A : Carrier) (hΓ : ArithmeticNamedAxiomComparison.ExtendsPA A) :
    (ℕ↓[ℒₒᵣ] ⊧ positiveSentence A) ∧ (ℕ↓[ℒₒᵣ] ⊧ negativeSentence A) :=
  standard_sentences_of_axioms_admissible A
    (ArithmeticNamedAxiomComparison.axiomsAdmissible_PA A hΓ)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable [M ≡ₑ[ℒₒᵣ] ℕ]

theorem semantic_positive (A : Carrier) (hΓ : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (n : M) (h : ArithmeticDiagonalCodes.alpha.val.Evalb ![n]) :
    (NamedArithmeticProofSearch.positive A namedAlpha).val.Evalb ![n] :=
  semantic_positive_of_axioms_admissible M A
    (ArithmeticNamedAxiomComparison.axiomsAdmissible_PA A hΓ) n h

theorem semantic_negative (A : Carrier) (hΓ : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (n : M) (h : ArithmeticDiagonalCodes.beta.val.Evalb ![n]) :
    (NamedArithmeticProofSearch.negative A namedAlpha).val.Evalb ![n] :=
  semantic_negative_of_axioms_admissible M A
    (ArithmeticNamedAxiomComparison.axiomsAdmissible_PA A hΓ) n h

/-- The two printed universal bounds refer to the selected literal
conclusion program, the actual numeral-substitution function Θ, and
the proved PA-total negation extension. -/
theorem semantic_bounds (A : Carrier) (hΓ : ArithmeticNamedAxiomComparison.ExtendsPA A) :
    (∀ n : M, ArithmeticDiagonalCodes.alpha.val.Evalb ![n] →
      (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound A).val.Evalb
          ![NamedArithmeticUnarySubstitution.value ArithmeticDiagonalCodes.alpha.val n]) ∧
    (∀ n : M, ArithmeticDiagonalCodes.beta.val.Evalb ![n] →
      (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound A).val.Evalb
          ![NamedArithmeticProofSearch.negationWord M
            (NamedArithmeticUnarySubstitution.value ArithmeticDiagonalCodes.alpha.val n)]) := by
  constructor
  · intro n hn
    exact (NamedArithmeticProofSearch.positive_eval M A namedAlpha n).mp
      (semantic_positive M A hΓ n hn)
  · intro n hn
    exact (NamedArithmeticProofSearch.negative_eval_word M A namedAlpha
      namedAlpha_freeVariables n).mp (semantic_negative M A hΓ n hn)

theorem model_positive (A : Carrier) (hΓ : ArithmeticNamedAxiomComparison.ExtendsPA A) :
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem ArithmeticDiagonalCodes.a0 ≤
      (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
        (Idem.pull (NamedArithmeticProofSearch.sourceTheta namedAlpha namedAlpha_freeVariables)
          (predicateIdem 𝗣𝗔 (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound A))) :=
  model_positive_of_axioms_admissible M A
    (ArithmeticNamedAxiomComparison.axiomsAdmissible_PA A hΓ)

theorem model_negative (A : Carrier) (hΓ : ArithmeticNamedAxiomComparison.ExtendsPA A) :
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem ArithmeticDiagonalCodes.a1 ≤
      (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
        (Idem.pull (NamedArithmeticProofSearch.sourceTheta namedAlpha namedAlpha_freeVariables)
          (predicateIdem 𝗣𝗔 (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound A))) :=
  model_negative_of_axioms_admissible M A
    (ArithmeticNamedAxiomComparison.axiomsAdmissible_PA A hΓ)

end Models
end CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds
