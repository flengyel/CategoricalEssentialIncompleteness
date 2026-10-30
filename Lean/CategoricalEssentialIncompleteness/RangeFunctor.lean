/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.LocalSwitch

/-! # Range functors and their canonical coproduct comparison -/

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms zero_comp comp_zero)
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness

variable {R : Type u₁} {A : Type u₂} [Category.{v₁} R] [Category.{v₂} A]
variable [RestrictionCategory R] [RestrictionCategory A]
variable [Ranges R] [Ranges A]
variable [CoprodStruct R] [CategoryTheory.HasCoproducts R]
variable [CoprodStruct A] [CategoryTheory.HasCoproducts A]
variable [HasZeroMorphisms R] [HasZeroMorphisms A]

def coproductComparison (F : R ⥤ A) (X Y : R) :
    coprod (F.obj X) (F.obj Y) ⟶ F.obj (coprod X Y) :=
  copair (F.map (i0 X Y)) (F.map (i1 X Y))

/-- Preservation of restrictions, ranges, zeros, and binary coproducts.
The comparison is the canonical map, rather than an arbitrary isomorphism. -/
structure RangeFunctor (R : Type u₁) (A : Type u₂)
    [Category.{v₁} R] [Category.{v₂} A] [RestrictionCategory R] [RestrictionCategory A]
    [Ranges R] [Ranges A] [CoprodStruct R] [CategoryTheory.HasCoproducts R]
    [CoprodStruct A] [CategoryTheory.HasCoproducts A]
    [HasZeroMorphisms R] [HasZeroMorphisms A] where
  toFunctor : R ⥤ A
  map_restrict : ∀ {X Y : R} (f : X ⟶ Y), toFunctor.map (rst f) = rst (toFunctor.map f)
  map_range : ∀ {X Y : R} (f : X ⟶ Y),
    toFunctor.map (Ranges.range f).hom = (Ranges.range (toFunctor.map f)).hom
  map_zero : ∀ X Y : R, toFunctor.map (0 : X ⟶ Y) = 0
  comparison_isIso : ∀ X Y : R, IsIso (coproductComparison toFunctor X Y)

namespace RangeFunctor

variable (F : RangeFunctor R A)

noncomputable def comparison (X Y : R) :
    coprod (F.toFunctor.obj X) (F.toFunctor.obj Y) ≅ F.toFunctor.obj (coprod X Y) := by
  letI := F.comparison_isIso X Y
  exact asIso (coproductComparison F.toFunctor X Y)

@[simp] theorem comparison_hom (X Y : R) :
    (F.comparison X Y).hom = coproductComparison F.toFunctor X Y := rfl

def mapIdem {X : R} (a : Idem X) : Idem (F.toFunctor.obj X) :=
  ⟨F.toFunctor.map a.hom, by rw [← F.map_restrict, a.restriction]⟩

@[simp] theorem mapIdem_hom {X : R} (a : Idem X) :
    (F.mapIdem a).hom = F.toFunctor.map a.hom := rfl

theorem map_total {X Y : R} (f : X ⟶ Y) (hf : isTotal f) : isTotal (F.toFunctor.map f) := by
  change rst (F.toFunctor.map f) = 𝟙 _
  rw [← F.map_restrict, show rst f = 𝟙 X from hf, F.toFunctor.map_id]

@[simp] theorem map_top {X : R} : F.mapIdem (⊤ : Idem X) = ⊤ := by
  apply Idem.ext
  exact F.toFunctor.map_id X

@[simp] theorem map_inf {X : R} (a b : Idem X) :
    F.mapIdem (a ⊓ b) = F.mapIdem a ⊓ F.mapIdem b := by
  apply Idem.ext
  exact F.toFunctor.map_comp a.hom b.hom

theorem map_mono {X : R} : Monotone (F.mapIdem (X := X)) := by
  intro a b hab
  have h := F.map_inf a b
  rw [inf_eq_left.mpr hab] at h
  exact inf_eq_left.mp h.symm

@[simp] theorem map_pull {X Y : R} (f : X ⟶ Y) (a : Idem Y) :
    F.mapIdem (Idem.pull f a) = Idem.pull (F.toFunctor.map f) (F.mapIdem a) := by
  apply Idem.ext
  change F.toFunctor.map (rst (f ≫ a.hom)) = rst (F.toFunctor.map f ≫ F.toFunctor.map a.hom)
  rw [F.map_restrict, F.toFunctor.map_comp]

@[simp] theorem i0_comparison (X Y : R) :
    i0 (F.toFunctor.obj X) (F.toFunctor.obj Y) ≫ (F.comparison X Y).hom =
      F.toFunctor.map (i0 X Y) := i0_copair _ _

@[simp] theorem i1_comparison (X Y : R) :
    i1 (F.toFunctor.obj X) (F.toFunctor.obj Y) ≫ (F.comparison X Y).hom =
      F.toFunctor.map (i1 X Y) := i1_copair _ _

theorem comparison_copair {X Y Z : R} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (F.comparison X Y).hom ≫ F.toFunctor.map (copair f g) =
      copair (F.toFunctor.map f) (F.toFunctor.map g) := by
  apply hom_ext
  · rw [← Category.assoc, i0_comparison, ← F.toFunctor.map_comp, i0_copair, i0_copair]
  · rw [← Category.assoc, i1_comparison, ← F.toFunctor.map_comp, i1_copair, i1_copair]

theorem comparison_sum {W X Y Z : R} (f : W ⟶ X) (g : Y ⟶ Z) :
    (F.comparison W Y).hom ≫ F.toFunctor.map (coprod_map f g) =
      coprod_map (F.toFunctor.map f) (F.toFunctor.map g) ≫ (F.comparison X Z).hom := by
  apply hom_ext
  · rw [← Category.assoc, i0_comparison, ← F.toFunctor.map_comp,
      i0_coprod_map, F.toFunctor.map_comp]
    rw [← Category.assoc, i0_coprod_map, Category.assoc, i0_comparison]
  · rw [← Category.assoc, i1_comparison, ← F.toFunctor.map_comp,
      i1_coprod_map, F.toFunctor.map_comp]
    rw [← Category.assoc, i1_coprod_map, Category.assoc, i1_comparison]

theorem comparison_inv_sum {W X Y Z : R} (f : W ⟶ X) (g : Y ⟶ Z) :
    (F.comparison W Y).inv ≫ coprod_map (F.toFunctor.map f) (F.toFunctor.map g) =
      F.toFunctor.map (coprod_map f g) ≫ (F.comparison X Z).inv := by
  apply (cancel_epi (F.comparison W Y).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [F.comparison_sum, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem pull_comparison_inv_sum [RestrictionCoproducts R] [RestrictionCoproducts A]
    {X Y : R} (a : Idem X) (b : Idem Y) :
    Idem.pull (F.comparison X Y).inv ((F.mapIdem a).sum (F.mapIdem b)) =
      F.mapIdem (a.sum b) := by
  apply Idem.ext
  change rst ((F.comparison X Y).inv ≫
    coprod_map (F.toFunctor.map a.hom) (F.toFunctor.map b.hom)) =
      F.toFunctor.map (coprod_map a.hom b.hom)
  have hi : isTotal (F.comparison X Y).inv := iso_total (F.comparison X Y).symm
  rw [F.comparison_inv_sum, rst_comp_of_isTotal _ hi,
    ← F.map_restrict, restrict_sum, a.restriction, b.restriction]

variable [RestrictionZero R] [RestrictionZero A] [BinaryJoins R] [BinaryJoins A]

omit [BinaryJoins R] [BinaryJoins A] in
@[simp] theorem map_bot {X : R} : F.mapIdem (⊥ : Idem X) = ⊥ :=
  Idem.ext (F.map_zero X X)

omit [RestrictionZero R] [RestrictionZero A] in
theorem map_sup {X : R} (a b : Idem X) :
    F.mapIdem (a ⊔ b) = F.mapIdem a ⊔ F.mapIdem b := by
  apply Idem.ext
  change F.toFunctor.map (a ⊔ b).hom = (F.mapIdem a ⊔ F.mapIdem b).hom
  rw [← range_copair_idem, F.map_range, ← range_copair_idem]
  have h := Ranges.precomp_split_epi (F.comparison X X).hom (F.comparison X X).inv
    (F.comparison X X).inv_hom_id (F.toFunctor.map (copair a.hom b.hom))
  rw [F.comparison_copair] at h
  exact congrArg Idem.hom h.symm

theorem map_complementary {X : R} {c c' : Idem X} (hc : Complementary c c') :
    Complementary (F.mapIdem c) (F.mapIdem c') := by
  constructor
  · rw [← F.map_inf, hc.disjoint, F.map_bot]
  · rw [← F.map_sup, hc.cover, F.map_top]

end RangeFunctor

end CategoricalEssentialIncompleteness.LocalConnectedness
