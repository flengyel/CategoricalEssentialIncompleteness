/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RestrictionProductCategory
public import PCats.Recursion

/-! # Zero absorption for binary restriction products -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.RestrictionProducts.ProductData

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]
variable [HasZeroMorphisms C] [RestrictionZero C] (D : ProductData C)

theorem pair_zero_right {V X Y : C} (f : V ⟶ X) : D.pair f (0 : V ⟶ Y) = 0 := by
  apply D.hom_ext
  · rw [D.pair_fst, RestrictionZero.restrict_zero, zero_comp, zero_comp]
  · rw [D.pair_snd, comp_zero, zero_comp]

theorem pair_zero_left {V X Y : C} (g : V ⟶ Y) : D.pair (0 : V ⟶ X) g = 0 := by
  apply D.hom_ext
  · rw [D.pair_fst, comp_zero, zero_comp]
  · rw [D.pair_snd, RestrictionZero.restrict_zero, zero_comp, zero_comp]

theorem prodominicalLaws : @RecursionCategory.Prodominical C inferInstance
    D.pcategoryStruct inferInstance := by
  let : PCategoryStruct C := D.pcategoryStruct
  exact {
    nearProd_zero_right f := by
      change D.pair (D.fst _ _ ≫ f) (D.snd _ _ ≫ 0) = 0
      rw [comp_zero, D.pair_zero_right]
    nearProd_zero_left f := by
      change D.pair (D.fst _ _ ≫ 0) (D.snd _ _ ≫ f) = 0
      rw [comp_zero, D.pair_zero_left]
  }

end CategoricalEssentialIncompleteness.V46.RestrictionProducts.ProductData
