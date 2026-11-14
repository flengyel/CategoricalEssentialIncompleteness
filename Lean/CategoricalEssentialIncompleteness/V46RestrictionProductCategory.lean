/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RestrictionProductData

/-! # The P-category structure determined by binary restriction products -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.V46.RestrictionProducts.ProductData

variable {C : Type u} [Category.{v} C] [RestrictionCategory C] (D : ProductData C)

def associator (X Y Z : C) : D.prod (D.prod X Y) Z ⟶ D.prod X (D.prod Y Z) :=
  D.pair (D.fst (D.prod X Y) Z ≫ D.fst X Y)
    (D.pair (D.fst (D.prod X Y) Z ≫ D.snd X Y) (D.snd (D.prod X Y) Z))

theorem pair_associator {V X Y Z : C} (f : V ⟶ X) (g : V ⟶ Y) (h : V ⟶ Z) :
    D.pair (D.pair f g) h ≫ D.associator X Y Z = D.pair f (D.pair g h) := by
  let A := D.pair (D.pair f g) h
  have h0 : A ≫ (D.fst (D.prod X Y) Z ≫ D.fst X Y) = rst (D.pair g h) ≫ f := by
    change D.pair (D.pair f g) h ≫ _ = _
    rw [← Category.assoc, D.pair_fst, Category.assoc, D.pair_fst,
      D.pair_restriction, ← Category.assoc]
    exact congrArg (fun k => k ≫ f) (rst_comm h g)
  have h1 : D.pair (A ≫ (D.fst (D.prod X Y) Z ≫ D.snd X Y))
      (A ≫ D.snd (D.prod X Y) Z) = rst f ≫ D.pair g h := by
    change D.pair
      (D.pair (D.pair f g) h ≫ (D.fst (D.prod X Y) Z ≫ D.snd X Y))
      (D.pair (D.pair f g) h ≫ D.snd (D.prod X Y) Z) = _
    rw [← Category.assoc, D.pair_fst, Category.assoc, D.pair_snd,
      D.pair_snd, D.pair_restriction]
    calc
      _ = D.pair (rst f ≫ (rst h ≫ g)) (rst f ≫ (rst g ≫ h)) := by
        rw [← Category.assoc, rst_comm h f]
        simp only [Category.assoc]
      _ = rst f ≫ D.pair (rst h ≫ g) (rst g ≫ h) := (D.comp_pair _ _ _).symm
      _ = _ := congrArg (fun k => rst f ≫ k) (D.pair_mask g h)
  change A ≫ D.pair _ (D.pair _ _) = _
  rw [D.comp_pair, D.comp_pair, h0, h1, D.pair_mask]

theorem associator_nat {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    D.map (D.map f g) h ≫ D.associator X' Y' Z' =
      D.associator X Y Z ≫ D.map f (D.map g h) := by
  have hm : D.map (D.map f g) h =
      D.pair (D.pair ((D.fst (D.prod X Y) Z ≫ D.fst X Y) ≫ f)
        ((D.fst (D.prod X Y) Z ≫ D.snd X Y) ≫ g)) (D.snd (D.prod X Y) Z ≫ h) := by
    change D.pair (D.fst (D.prod X Y) Z ≫ D.pair _ _) _ = _
    rw [D.comp_pair]
    simp only [Category.assoc]
  rw [hm, D.pair_associator]
  change _ = D.pair _ (D.pair _ _) ≫ D.map f (D.map g h)
  rw [D.pair_comp_map, D.pair_comp_map]

def symmetry (X Y : C) : D.prod X Y ⟶ D.prod Y X := D.pair (D.snd X Y) (D.fst X Y)

theorem symmetry_nat {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    D.map f g ≫ D.symmetry X' Y' = D.symmetry X Y ≫ D.map g f := by
  unfold symmetry
  rw [D.comp_pair, D.pair_comp_map]
  change D.pair (D.pair _ _ ≫ D.snd X' Y') (D.pair _ _ ≫ D.fst X' Y') = _
  rw [D.pair_snd, D.pair_fst, D.pair_mask]

@[instance_reducible] def pcategoryStruct : PCategoryStruct C where
  nearProd := D.prod
  nearProd_map := D.map
  diag X := D.pair (𝟙 X) (𝟙 X)
  p0 := D.fst
  p1 := D.snd

theorem partialPairing_eq {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y) :
    @PCategoryStruct.partialPairing C inferInstance D.pcategoryStruct W X Y f g =
      D.pair f g := by
  change D.pair (𝟙 W) (𝟙 W) ≫ D.map f g = _
  rw [D.pair_comp_map, Category.id_comp, Category.id_comp]

theorem associator_eq (X Y Z : C) :
    @PCategoryStruct.assoc C inferInstance D.pcategoryStruct X Y Z = D.associator X Y Z := by
  unfold PCategoryStruct.assoc
  rw [D.partialPairing_eq, D.partialPairing_eq]
  rfl

theorem symmetry_eq (X Y : C) :
    @PCategoryStruct.swap C inferInstance D.pcategoryStruct X Y = D.symmetry X Y := by
  unfold PCategoryStruct.swap
  rw [D.partialPairing_eq]
  rfl

/-- Restriction products give all fourteen P-category laws. -/
theorem pcategoryLaws : @PCategory C inferInstance D.pcategoryStruct := by
  let : PCategoryStruct C := D.pcategoryStruct
  exact {
    nearProd_id := D.map_id
    nearProd_comp := D.map_comp
    diag_p0 X := by
      change D.pair (𝟙 X) (𝟙 X) ≫ D.fst X X = 𝟙 X
      rw [D.pair_fst, rst_id, Category.id_comp]
    diag_p1 X := by
      change D.pair (𝟙 X) (𝟙 X) ≫ D.snd X X = 𝟙 X
      rw [D.pair_snd, rst_id, Category.id_comp]
    diag_p0_p1 X Y := by
      change D.pair (𝟙 (D.prod X Y)) (𝟙 (D.prod X Y)) ≫ D.map (D.fst X Y) (D.snd X Y) =
        𝟙 (D.prod X Y)
      rw [D.pair_comp_map, Category.id_comp, Category.id_comp]
      simpa only [Category.id_comp] using D.pair_proj (𝟙 (D.prod X Y))
    p0_p0 X Y Z := by
      change D.map (𝟙 X) (D.fst Y Z) ≫ D.fst X Y = D.fst X (D.prod Y Z)
      rw [D.map_fst_of_total _ _ (D.fst_total Y Z), Category.comp_id]
    p0_p1 X Y Z := by
      change D.map (𝟙 X) (D.snd Y Z) ≫ D.fst X Z = D.fst X (D.prod Y Z)
      rw [D.map_fst_of_total _ _ (D.snd_total Y Z), Category.comp_id]
    p1_p0 X Y Z := by
      change D.map (D.fst X Y) (𝟙 Z) ≫ D.snd X Z = D.snd (D.prod X Y) Z
      rw [D.map_snd_of_total _ _ (D.fst_total X Y), Category.comp_id]
    p1_p1 X Y Z := by
      change D.map (D.snd X Y) (𝟙 Z) ≫ D.snd Y Z = D.snd (D.prod X Y) Z
      rw [D.map_snd_of_total _ _ (D.snd_total X Y), Category.comp_id]
    diag_nat f := by
      change f ≫ D.pair _ _ = D.pair _ _ ≫ D.map f f
      rw [D.comp_pair, D.pair_comp_map, Category.comp_id, Category.id_comp]
    p0_nat {X Y Z} f := D.map_fst_of_total f (𝟙 Z) (rst_id Z)
    p1_nat {X Y Z} f := D.map_snd_of_total (𝟙 Z) f (rst_id Z)
    assoc_nat f g h := by
      rw [D.associator_eq, D.associator_eq]
      exact D.associator_nat f g h
    swap_nat f g := by
      rw [D.symmetry_eq, D.symmetry_eq]
      exact D.symmetry_nat f g
  }

theorem restriction_eq {X Y : C} (f : X ⟶ Y) :
    @PCategoryStruct.rst C inferInstance D.pcategoryStruct X Y f = rst f := by
  unfold PCategoryStruct.rst
  rw [← Category.assoc]
  change (@PCategoryStruct.partialPairing C inferInstance D.pcategoryStruct X X Y (𝟙 X) f) ≫
    D.fst X Y = rst f
  rw [D.partialPairing_eq, D.pair_fst, Category.comp_id]

omit [RestrictionCategory C] in
private theorem restriction_ext (a b : RestrictionCategory C)
    (h : ∀ {X Y : C} (f : X ⟶ Y),
      @CategoryTheory.RestrictionCategory.rst C inferInstance a X Y f =
        @CategoryTheory.RestrictionCategory.rst C inferInstance b X Y f) : a = b := by
  cases a with
  | mk ra a1 a2 a3 a4 =>
    cases b with
    | mk rb b1 b2 b3 b4 =>
      have he : @ra = @rb := by
        funext X Y f
        exact h f
      cases he
      rfl

theorem restrictionCategory_eq :
    @PCategory.inducedRestriction C inferInstance D.pcategoryStruct D.pcategoryLaws =
      (inferInstance : RestrictionCategory C) :=
  restriction_ext _ _ (fun f => D.restriction_eq f)

end CategoricalEssentialIncompleteness.V46.RestrictionProducts.ProductData
