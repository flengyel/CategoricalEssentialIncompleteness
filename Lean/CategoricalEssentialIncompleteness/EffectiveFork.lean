/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EnumerableCarriers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-! # Partial recursive maps with subfunctor domains on the walking span -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms)

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork


/-- A functor from the walking span to the category of total recursive maps. -/
structure Object where
  center : EnumerableCarriers.Carrier
  left : EnumerableCarriers.Carrier
  right : EnumerableCarriers.Carrier
  leftMap : center ⟶ left
  rightMap : center ⟶ right
  left_total : isTotal leftMap
  right_total : isTotal rightMap

def totalDiagram (X : Object) : CategoryTheory.Limits.WalkingSpan ⥤ EnumerableCarriers.Total :=
  CategoryTheory.Limits.span
    (⟨X.leftMap, X.left_total⟩ : (⟨X.center⟩ : EnumerableCarriers.Total) ⟶ ⟨X.left⟩)
    (⟨X.rightMap, X.right_total⟩ : (⟨X.center⟩ : EnumerableCarriers.Total) ⟶ ⟨X.right⟩)

/-- Naturality on the domain, including forward closure of that domain. -/
def Respects {C A D B : EnumerableCarriers.Carrier} (r : C ⟶ A) (s : D ⟶ B)
    (f : C ⟶ D) (g : A ⟶ B) : Prop :=
  ∀ x y u v : ℕ, y ∈ EnumerableCarriers.val f x → u ∈ EnumerableCarriers.val r x → v ∈ EnumerableCarriers.val s y → v ∈ EnumerableCarriers.val g u

theorem respects_id {C A : EnumerableCarriers.Carrier} (r : C ⟶ A) : Respects r r (𝟙 C) (𝟙 A) := by
  intro x y u v hxy hxu hyv
  obtain ⟨_, he⟩ := (mem_supportIdentity C.support x y).mp hxy
  subst y
  have he : v = u := Part.mem_unique hyv hxu
  exact (mem_supportIdentity A.support u v).mpr
    ⟨EnumerableCarriers.val_target r x u hxu, he⟩

theorem respects_comp {C A D B K L : EnumerableCarriers.Carrier}
    {r : C ⟶ A} {s : D ⟶ B} {t : K ⟶ L}
    {f : C ⟶ D} {g : A ⟶ B} {h : D ⟶ K} {k : B ⟶ L}
    (st : isTotal s) (hf : Respects r s f g) (hh : Respects s t h k) :
    Respects r t (f ≫ h) (g ≫ k) := by
  intro x z u w hxz hxu hzw
  obtain ⟨y, hxy, hyz⟩ := (EnumerableCarriers.mem_val_comp f h x z).mp hxz
  have hd := (EnumerableCarriers.total_iff s).mp st y (EnumerableCarriers.val_target f x y hxy)
  obtain ⟨v, hyv⟩ := Part.dom_iff_mem.mp hd
  exact (EnumerableCarriers.mem_val_comp g k u w).mpr ⟨v, hf x y u v hxy hxu hyv,
    hh y z v w hyz hyv hzw⟩

theorem respects_restriction {C A D B : EnumerableCarriers.Carrier}
    {r : C ⟶ A} {s : D ⟶ B} {f : C ⟶ D} {g : A ⟶ B}
    (st : isTotal s) (hf : Respects r s f g) : Respects r r (rst f) (rst g) := by
  intro x y u v hxy hxu hyv
  obtain ⟨⟨z, hxz⟩, he⟩ := (EnumerableCarriers.mem_val_restriction f x y).mp hxy
  subst y
  have hd := (EnumerableCarriers.total_iff s).mp st z (EnumerableCarriers.val_target f x z hxz)
  obtain ⟨w, hzw⟩ := Part.dom_iff_mem.mp hd
  exact (EnumerableCarriers.mem_val_restriction g u v).mpr
    ⟨⟨w, hf x z u w hxz hxu hzw⟩, Part.mem_unique hyv hxu⟩

@[ext] structure Hom (X Y : Object) where
  center : X.center ⟶ Y.center
  left : X.left ⟶ Y.left
  right : X.right ⟶ Y.right
  natural_left : Respects X.leftMap Y.leftMap center left
  natural_right : Respects X.rightMap Y.rightMap center right

instance : Category Object where
  Hom := Hom
  id X := ⟨𝟙 _, 𝟙 _, 𝟙 _, respects_id _, respects_id _⟩
  comp {X Y Z} f g := ⟨f.center ≫ g.center, f.left ≫ g.left, f.right ≫ g.right,
    respects_comp Y.left_total f.natural_left g.natural_left,
    respects_comp Y.right_total f.natural_right g.natural_right⟩
  id_comp f := Hom.ext (Category.id_comp _) (Category.id_comp _) (Category.id_comp _)
  comp_id f := Hom.ext (Category.comp_id _) (Category.comp_id _) (Category.comp_id _)
  assoc f g h := Hom.ext (Category.assoc _ _ _) (Category.assoc _ _ _) (Category.assoc _ _ _)

def center : Object ⥤ EnumerableCarriers.Carrier where
  obj := Object.center
  map := Hom.center

def left : Object ⥤ EnumerableCarriers.Carrier where
  obj := Object.left
  map := Hom.left

def right : Object ⥤ EnumerableCarriers.Carrier where
  obj := Object.right
  map := Hom.right

instance forkRestriction : RestrictionCategory Object where
  rst {X Y} f := ⟨rst f.center, rst f.left, rst f.right,
    respects_restriction Y.left_total f.natural_left,
    respects_restriction Y.right_total f.natural_right⟩
  rst_comp_self f := Hom.ext (rst_comp_self _) (rst_comp_self _) (rst_comp_self _)
  rst_comm f g := Hom.ext (rst_comm _ _) (rst_comm _ _) (rst_comm _ _)
  rst_comp_rst f g := Hom.ext (rst_comp_rst _ _) (rst_comp_rst _ _) (rst_comp_rst _ _)
  rst_comp f g := Hom.ext (rst_comp _ _) (rst_comp _ _) (rst_comp _ _)

attribute [instance 2000] forkRestriction

instance : HasZeroMorphisms Object where
  zero X Y := ⟨⟨0, 0, 0, fun _ _ _ _ h _ _ => False.elim (Part.notMem_none _ h),
    fun _ _ _ _ h _ _ => False.elim (Part.notMem_none _ h)⟩⟩
  comp_zero := by
    intros
    exact Hom.ext (CategoryTheory.Limits.comp_zero (C := EnumerableCarriers.Carrier))
      (CategoryTheory.Limits.comp_zero (C := EnumerableCarriers.Carrier))
      (CategoryTheory.Limits.comp_zero (C := EnumerableCarriers.Carrier))
  zero_comp := by
    intros
    exact Hom.ext (CategoryTheory.Limits.zero_comp (C := EnumerableCarriers.Carrier))
      (CategoryTheory.Limits.zero_comp (C := EnumerableCarriers.Carrier))
      (CategoryTheory.Limits.zero_comp (C := EnumerableCarriers.Carrier))

instance : RestrictionZero Object where
  restrict_zero X Y := Hom.ext (RestrictionZero.restrict_zero X.center Y.center)
    (RestrictionZero.restrict_zero X.left Y.left)
    (RestrictionZero.restrict_zero X.right Y.right)

theorem total_iff {X Y : Object} (f : X ⟶ Y) :
    isTotal f ↔ isTotal f.center ∧ isTotal f.left ∧ isTotal f.right := by
  constructor
  · intro h
    exact ⟨congrArg Hom.center h, congrArg Hom.left h, congrArg Hom.right h⟩
  · rintro ⟨hc, hl, hr⟩
    exact Hom.ext hc hl hr

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
