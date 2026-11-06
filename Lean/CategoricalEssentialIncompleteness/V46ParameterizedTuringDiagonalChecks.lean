import CategoricalEssentialIncompleteness.V46ParameterizedTuringDiagonal
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory PCategoryStruct
open CategoryTheory.CoprodStruct
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedRecursionCategory
open FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ParameterizedTuringDiagonal.Checks
example (ℓ : nearProd (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔) ⟶
    coprod (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)) :
    ∃ g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔, isTotal g ∧
      g ≫ diag (omegaObject 𝗣𝗔) ≫ ArithmeticDiagonalCodes.sourceTau ≫
        (omegaCoprodIso 𝗣𝗔).inv =
          partialPairing (𝟙 (omegaObject 𝗣𝗔)) g ≫ ℓ :=
  arithmetic_parameter_diagonal ℓ
end CategoricalEssentialIncompleteness.V46.ParameterizedTuringDiagonal.Checks
