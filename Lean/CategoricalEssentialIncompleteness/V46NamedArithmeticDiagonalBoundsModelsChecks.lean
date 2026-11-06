import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalBoundsModels

/-! # Whole-carrier source inverse-image order checks -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.NamedArithmeticSignature
open CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds.ModelsChecks

example (A : Carrier)
    (hPA : ∀ ψ ∈ 𝗣𝗔, SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] ψ))
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M ≡ₑ[ℒₒᵣ] ℕ] :
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem ArithmeticDiagonalCodes.a0 ≤
      (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
        (Idem.pull (NamedArithmeticProofSearch.sourceTheta
          (NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val)
          (NamedArithmeticUnarySubstitution.namedFormula_freeVariables
            ArithmeticDiagonalCodes.alpha.val))
          (predicateIdem 𝗣𝗔 (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound A))) :=
  model_positive_of_axioms_admissible M A hPA

example (A : Carrier)
    (hPA : ∀ ψ ∈ 𝗣𝗔, SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] ψ))
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M ≡ₑ[ℒₒᵣ] ℕ] :
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem ArithmeticDiagonalCodes.a1 ≤
      (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
        (Idem.pull (NamedArithmeticProofSearch.sourceTheta
          (NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val)
          (NamedArithmeticUnarySubstitution.namedFormula_freeVariables
            ArithmeticDiagonalCodes.alpha.val))
          (predicateIdem 𝗣𝗔 (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound A))) :=
  model_negative_of_axioms_admissible M A hPA

end CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds.ModelsChecks
