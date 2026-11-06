/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.LocalLifting
import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodesTuring

/-! # The parameterized source equation for uniform independent sentences -/
noncomputable section
universe u v
open CategoryTheory CategoryTheory.RestrictionCategory
open PCategoryStruct PCategory
namespace CategoricalEssentialIncompleteness.V46.ParameterizedTuringDiagonal

/-- A single total source parameter realizes the two-input partial map.
There is no choice of a different source morphism in each numeral fiber. -/
theorem parameter_diagonal {C : Type u} [Category.{v} C]
    [PCategoryStruct C] [PCategory C] {U V : C}
    (τ : nearProd U U ⟶ U) (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : U ≅ V) (ℓ : nearProd U U ⟶ V) :
    ∃ g : U ⟶ U, isTotal g ∧
      g ≫ diag U ≫ τ ≫ b.hom = partialPairing (𝟙 U) g ≫ ℓ := by
  obtain ⟨g,hg,hparam⟩ := hτ U (ℓ ≫ b.inv)
  refine ⟨g,hg,?_⟩
  have hdiag : partialPairing (𝟙 U) g ≫ nearProd_map g (𝟙 U) = g ≫ diag U := by
    rw [partialPairing_comp_nearProd_map,Category.id_comp,Category.comp_id]
    simpa only [Category.comp_id,partialPairing_id_id] using
      (comp_partialPairing g (𝟙 U) (𝟙 U)).symm
  have he := congrArg (fun k => partialPairing (𝟙 U) g ≫ k ≫ b.hom) hparam
  simp only [← Category.assoc] at he
  rw [hdiag] at he
  simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using he

open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedRecursionCategory
open CategoryTheory.CoprodStruct
open FFL.FirstOrder.Arithmetic

/-- The fixed S_PA universal morphism gives the precise source equation
used by the uniform arithmetic construction. The supplied lift is partial. -/
theorem arithmetic_parameter_diagonal
    (ℓ : nearProd (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔) ⟶
      coprod (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔)) :
    ∃ g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔, isTotal g ∧
      g ≫ diag (omegaObject 𝗣𝗔) ≫ ArithmeticDiagonalCodes.sourceTau ≫
        (omegaCoprodIso 𝗣𝗔).inv =
          partialPairing (𝟙 (omegaObject 𝗣𝗔)) g ≫ ℓ :=
  parameter_diagonal ArithmeticDiagonalCodes.sourceTau
    ArithmeticDiagonalCodes.sourceTau_isTuring (omegaCoprodIso 𝗣𝗔).symm ℓ

end CategoricalEssentialIncompleteness.V46.ParameterizedTuringDiagonal
