/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalBoundsSentences
import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodesModels
import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchSource

/-! # Interpreted diagonal bounds for the actual source inverse images -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds

open NamedArithmeticSignature

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable [M ≡ₑ[ℒₒᵣ] ℕ]

/-- The bound is an order relation on the full interpreted natural-number
carrier. Its right side interprets the actual source theorem inverse image. -/
theorem model_positive_of_axioms_admissible (A : Carrier)
    (hPA : ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔) :
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem ArithmeticDiagonalCodes.a0 ≤
      (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
        (Idem.pull (NamedArithmeticProofSearch.sourceTheta namedAlpha namedAlpha_freeVariables)
          (predicateIdem 𝗣𝗔 (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound A))) := by
  rw [ArithmeticDiagonalCodes.model_a0,
    NamedArithmeticProofSearch.positive_source_pull_model]
  apply (le_iff_support _ _).mpr
  rw [support_setIdem,support_setIdem]
  exact semantic_positive_of_axioms_admissible M A hPA

/-- The second diagonal domain is contained in the actual source
refutation inverse image, at every internal code of the model. -/
theorem model_negative_of_axioms_admissible (A : Carrier)
    (hPA : ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔) :
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem ArithmeticDiagonalCodes.a1 ≤
      (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
        (Idem.pull (NamedArithmeticProofSearch.sourceTheta namedAlpha namedAlpha_freeVariables)
          (predicateIdem 𝗣𝗔 (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound A))) := by
  rw [ArithmeticDiagonalCodes.model_a1,
    NamedArithmeticProofSearch.negative_source_pull_model]
  apply (le_iff_support _ _).mpr
  rw [support_setIdem,support_setIdem]
  exact semantic_negative_of_axioms_admissible M A hPA

end Models
end CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds
