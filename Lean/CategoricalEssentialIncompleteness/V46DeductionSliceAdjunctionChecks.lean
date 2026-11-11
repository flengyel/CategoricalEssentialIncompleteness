/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DeductionSliceAdjunction

/-! # Statement checks for the deduction comparison -/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46

open DeductionSliceAdjunction

variable {D₁ : Type u₁} {D₂ : Type u₂}
variable [Category.{v₁} D₁] [Category.{v₂} D₂] [Regular D₁] [Regular D₂]
variable {G : D₁ ⥤ D₂} {H : D₂ ⥤ D₁} (adj : G ⊣ H)
variable {S₁ : D₁} {S₂ : D₂} (σ : G.obj S₁ ⟶ S₂)

example : DeductionComparison.presentationFunctor G σ ⊣
    Over.post H ⋙ Over.pullback (adj.unit.app S₁ ≫ H.map σ) := adjunction adj σ

example (B : Subobject S₂) : (rightOrder adj σ).obj B = rightObject adj σ B := rfl

example : DeductionComparison.imageFunctor G σ ⊣ rightOrder adj σ := orderAdjunction adj σ

example (A : Subobject S₁) (B : Subobject S₂) :
    DeductionComparison.imageObject G σ A ≤ B ↔ A ≤ rightObject adj σ B :=
  order_galois adj σ A B

#print axioms CategoricalEssentialIncompleteness.V46.DeductionSliceAdjunction.rightIso
#print axioms CategoricalEssentialIncompleteness.V46.DeductionSliceAdjunction.adjunction
#print axioms CategoricalEssentialIncompleteness.V46.DeductionSliceAdjunction.order_galois
#print axioms CategoricalEssentialIncompleteness.V46.DeductionSliceAdjunction.orderAdjunction
