/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.LocalSwitch
public import PCats.PCat

/-! # Restriction products and their partial pairing calculus -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.RestrictionProducts

variable (C : Type u) [Category.{v} C] [RestrictionCategory C]

/-- Binary restriction products, specified by their partial pairing laws. -/
structure ProductData where
  prod : C → C → C
  fst : ∀ X Y, prod X Y ⟶ X
  snd : ∀ X Y, prod X Y ⟶ Y
  pair : ∀ {W X Y}, (W ⟶ X) → (W ⟶ Y) → (W ⟶ prod X Y)
  fst_total : ∀ X Y, isTotal (fst X Y)
  snd_total : ∀ X Y, isTotal (snd X Y)
  pair_fst : ∀ {W X Y} (f : W ⟶ X) (g : W ⟶ Y), pair f g ≫ fst X Y = rst g ≫ f
  pair_snd : ∀ {W X Y} (f : W ⟶ X) (g : W ⟶ Y), pair f g ≫ snd X Y = rst f ≫ g
  pair_restriction : ∀ {W X Y} (f : W ⟶ X) (g : W ⟶ Y), rst (pair f g) = rst f ≫ rst g
  pair_proj : ∀ {W X Y} (h : W ⟶ prod X Y), pair (h ≫ fst X Y) (h ≫ snd X Y) = h

namespace ProductData

variable {C} (D : ProductData C)

theorem hom_ext {W X Y : C} {h k : W ⟶ D.prod X Y}
    (h0 : h ≫ D.fst X Y = k ≫ D.fst X Y)
    (h1 : h ≫ D.snd X Y = k ≫ D.snd X Y) : h = k := by
  rw [← D.pair_proj h, ← D.pair_proj k, h0, h1]

theorem comp_pair {V W X Y : C} (h : V ⟶ W) (f : W ⟶ X) (g : W ⟶ Y) :
    h ≫ D.pair f g = D.pair (h ≫ f) (h ≫ g) := by
  apply D.hom_ext
  · rw [Category.assoc, D.pair_fst, D.pair_fst]
    simpa only [Category.assoc] using (congrArg (fun k => k ≫ f) (rst_comp h g)).symm
  · rw [Category.assoc, D.pair_snd, D.pair_snd]
    simpa only [Category.assoc] using (congrArg (fun k => k ≫ g) (rst_comp h f)).symm

theorem pair_restrict_left {W X Y : C} (a : Idem W) (f : W ⟶ X) (g : W ⟶ Y) :
    D.pair (a.hom ≫ f) g = a.hom ≫ D.pair f g := by
  apply D.hom_ext
  · rw [D.pair_fst, Category.assoc, D.pair_fst, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun k => k ≫ f) (Idem.comm a (Idem.ofRestrict g)).symm
  · rw [D.pair_snd, ← a.restriction, rst_comp_rst, a.restriction,
      Category.assoc, Category.assoc, D.pair_snd]

theorem pair_restrict_right {W X Y : C} (a : Idem W) (f : W ⟶ X) (g : W ⟶ Y) :
    D.pair f (a.hom ≫ g) = a.hom ≫ D.pair f g := by
  apply D.hom_ext
  · rw [D.pair_fst, ← a.restriction, rst_comp_rst, a.restriction,
      Category.assoc, Category.assoc, D.pair_fst]
  · rw [D.pair_snd, Category.assoc, D.pair_snd, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun k => k ≫ g) (Idem.comm a (Idem.ofRestrict f)).symm

theorem pair_absorb_left {W X Y : C} (a : Idem W) (f : W ⟶ X) (g : W ⟶ Y)
    (ha : a.hom ≫ f = f) : a.hom ≫ D.pair f g = D.pair f g := by
  rw [← D.pair_restrict_left, ha]

theorem pair_absorb_right {W X Y : C} (a : Idem W) (f : W ⟶ X) (g : W ⟶ Y)
    (ha : a.hom ≫ g = g) : a.hom ≫ D.pair f g = D.pair f g := by
  rw [← D.pair_restrict_right, ha]

theorem pair_cross_masks {W X Y X' Y' : C} (f : W ⟶ X) (g : W ⟶ Y)
    (a : X ⟶ X') (b : Y ⟶ Y') :
    D.pair (rst g ≫ (f ≫ a)) (rst f ≫ (g ≫ b)) = D.pair (f ≫ a) (g ≫ b) := by
  calc
    _ = rst g ≫ D.pair (f ≫ a) (rst f ≫ (g ≫ b)) :=
      D.pair_restrict_left (Idem.ofRestrict g) _ _
    _ = rst g ≫ (rst f ≫ D.pair (f ≫ a) (g ≫ b)) :=
      congrArg (fun k => rst g ≫ k) (D.pair_restrict_right (Idem.ofRestrict f) _ _)
    _ = rst g ≫ D.pair (f ≫ a) (g ≫ b) :=
      congrArg (fun k => rst g ≫ k) (D.pair_absorb_left (Idem.ofRestrict f) _ _ (by
        change rst f ≫ (f ≫ a) = f ≫ a
        rw [← Category.assoc, rst_comp_self]))
    _ = _ := D.pair_absorb_right (Idem.ofRestrict g) _ _ (by
      change rst g ≫ (g ≫ b) = g ≫ b
      rw [← Category.assoc, rst_comp_self])

theorem pair_mask {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y) :
    D.pair (rst g ≫ f) (rst f ≫ g) = D.pair f g := by
  simpa only [D.pair_fst, D.pair_snd] using D.pair_proj (D.pair f g)

def map {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : D.prod W Y ⟶ D.prod X Z :=
  D.pair (D.fst W Y ≫ f) (D.snd W Y ≫ g)

theorem pair_comp_map {V W X Y Z : C} (f : V ⟶ W) (g : V ⟶ X)
    (a : W ⟶ Y) (b : X ⟶ Z) :
    D.pair f g ≫ D.map a b = D.pair (f ≫ a) (g ≫ b) := by
  unfold map
  rw [D.comp_pair]
  simp only [← Category.assoc, D.pair_fst, D.pair_snd]
  simpa only [Category.assoc] using D.pair_cross_masks f g a b

theorem map_comp {U V W X Y Z : C} (f : U ⟶ V) (g : V ⟶ W) (h : X ⟶ Y) (k : Y ⟶ Z) :
    D.map f h ≫ D.map g k = D.map (f ≫ g) (h ≫ k) := by
  change D.pair _ _ ≫ D.map g k = _
  rw [D.pair_comp_map]
  simp only [map, Category.assoc]

theorem map_id (X Y : C) : D.map (𝟙 X) (𝟙 Y) = 𝟙 (D.prod X Y) := by
  unfold map
  simpa only [Category.id_comp, Category.comp_id] using D.pair_proj (𝟙 (D.prod X Y))

theorem map_fst_of_total {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) (hg : isTotal g) :
    D.map f g ≫ D.fst X Z = D.fst W Y ≫ f := by
  unfold map
  rw [D.pair_fst, show rst (D.snd W Y ≫ g) = 𝟙 _ from
    isTotal_comp (D.snd_total W Y) hg, Category.id_comp]

theorem map_snd_of_total {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) (hf : isTotal f) :
    D.map f g ≫ D.snd X Z = D.snd W Y ≫ g := by
  unfold map
  rw [D.pair_snd, show rst (D.fst W Y ≫ f) = 𝟙 _ from
    isTotal_comp (D.fst_total W Y) hf, Category.id_comp]

end ProductData
end CategoricalEssentialIncompleteness.V46.RestrictionProducts
