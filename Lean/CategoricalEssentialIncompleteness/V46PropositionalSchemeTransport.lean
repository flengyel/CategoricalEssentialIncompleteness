/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ErasureLogicalSchemes
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # The three propositional schemes under the product comparisons -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.PropositionalSchemeTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [Regular D]
variable (K : C ⥤ D) [PreservesFiniteProducts K]
variable {X U V W : C}

def implication (i : X ⨯ X ⟶ X) : K.obj X ⨯ K.obj X ⟶ K.obj X :=
  inv (prodComparison K X X) ≫ K.map i

omit [Regular D] in
@[reassoc] theorem map_lift_comparison (f : W ⟶ U) (g : W ⟶ V) :
    K.map (prod.lift f g) ≫ prodComparison K U V = prod.lift (K.map f) (K.map g) := by
  apply prod.hom_ext <;> simp [← K.map_comp]

omit [Regular D] in
theorem map_pair_imp (i : X ⨯ X ⟶ X) (f g : W ⟶ X) :
    K.map (prod.lift f g ≫ i) =
      prod.lift (K.map f) (K.map g) ≫ implication K i := by
  rw [implication, ← map_lift_comparison_assoc]
  simp only [IsIso.hom_inv_id_assoc, K.map_comp]

def ternaryComparison (X : C) :
    K.obj ((X ⨯ X) ⨯ X) ⟶ (K.obj X ⨯ K.obj X) ⨯ K.obj X :=
  prodComparison K (X ⨯ X) X ≫ prod.map (prodComparison K X X) (𝟙 _)

theorem one (i : X ⨯ X ⟶ X) : K.map (ErasureLogicalSchemes.one i) =
    prodComparison K X X ≫ ErasureLogicalSchemes.one (implication K i) := by
  simp only [ErasureLogicalSchemes.one, map_pair_imp]
  simp [prod.comp_lift_assoc]

theorem two (i : X ⨯ X ⟶ X) : K.map (ErasureLogicalSchemes.two i) =
    ternaryComparison K X ≫ ErasureLogicalSchemes.two (implication K i) := by
  have hi : K.map i = prodComparison K X X ≫ implication K i := by
    simp [implication]
  simp only [ErasureLogicalSchemes.two, map_pair_imp]
  simp [ternaryComparison, prod.comp_lift_assoc, Category.assoc, K.map_comp, hi]

theorem three (n : X ⟶ X) (i : X ⨯ X ⟶ X) :
    K.map (ErasureLogicalSchemes.three n i) = prodComparison K X X ≫
      ErasureLogicalSchemes.three (K.map n) (implication K i) := by
  have hi : K.map i = prodComparison K X X ≫ implication K i := by
    simp [implication]
  simp only [ErasureLogicalSchemes.three, map_pair_imp]
  simp [prod.comp_lift_assoc, K.map_comp, hi]

end CategoricalEssentialIncompleteness.V46.PropositionalSchemeTransport
