/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ParameterizedTuringDiagonal


/-! # The parameterized source equation for uniform independent sentences -/

@[expose] public section
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
