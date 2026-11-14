/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46AmbientPartialSlice
public import CategoricalEssentialIncompleteness.RestrictionFunctorEquivalences

/-! # Postcomposition between partial slices -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialSlicePostcompose

open RestrictionSubobjects AmbientPartialSlice
variable {C : Type u} [Category.{v} C] [RestrictionCategory C]
variable {T U V : Tot C} (i : T ⟶ U)

def object (X : Family T.obj) : Family U.obj :=
  ⟨X.base, X.proj ≫ i.hom, isTotal_comp X.total i.property⟩

def map {X Y : Family T.obj} (f : X ⟶ Y) : object i X ⟶ object i Y :=
  ⟨f.hom, by
    change f.hom ≫ (Y.proj ≫ i.hom) = rst f.hom ≫ (X.proj ≫ i.hom)
    rw [← Category.assoc, f.over, Category.assoc]⟩

def functor : Family T.obj ⥤ Family U.obj where
  obj := object i
  map := map i

omit i in
theorem family_ext {P : C} {X Y : Family P} (hb : X.base = Y.base)
    (hp : HEq X.proj Y.proj) : X = Y := by
  cases X
  cases Y
  cases hb
  cases hp
  rfl

omit i in
theorem eqToHom_hom {P : C} {X Y : Family P} (h : X = Y) :
    (eqToHom h).hom = eqToHom (congrArg Family.base h) := by
  cases h
  rfl

theorem compose (j : U ⟶ V) : functor i ⋙ functor j = functor (i ≫ j) := by
  refine CategoryTheory.Functor.ext (F := functor i ⋙ functor j) (G := functor (i ≫ j)) ?_ ?_
  · intro X
    exact family_ext (X := object j (object i X)) (Y := object (i ≫ j) X)
      rfl (heq_of_eq (Category.assoc X.proj i.hom j.hom))
  · intro X Y f
    apply Hom.ext
    simp only [comp_hom, eqToHom_hom, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

omit i in
theorem identity (P : Tot C) : functor (𝟙 P) = 𝟭 (Family P.obj) := by
  refine CategoryTheory.Functor.ext (F := functor (𝟙 P)) (G := 𝟭 (Family P.obj)) ?_ ?_
  · intro X
    exact family_ext (X := object (𝟙 P) X) (Y := X) rfl (heq_of_eq (Category.comp_id X.proj))
  · intro X Y f
    apply Hom.ext
    simp only [comp_hom, eqToHom_hom, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

instance faithful : (functor i).Faithful where
  map_injective {X Y} f g h := by
    apply Hom.ext
    exact congrArg (fun k : object i X ⟶ object i Y => k.hom) h

theorem preserves_restriction : PreservesRestriction (functor i) := fun _ => rfl

theorem total_iff {X Y : Family T.obj} (f : X ⟶ Y) :
    isTotal ((functor i).map f) ↔ isTotal f := by
  rw [AmbientPartialSlice.total_iff, AmbientPartialSlice.total_iff]
  rfl

variable (inverses : MonoInverses C) [Mono i]

include inverses in
theorem full : (functor i).Full where
  map_surjective {X Y} f := by
    let g : X ⟶ Y := ⟨f.hom, by
      have h := congrArg (fun k => k ≫ inverse inverses i) f.over
      change (f.hom ≫ (Y.proj ≫ i.hom)) ≫ inverse inverses i =
        (rst f.hom ≫ (X.proj ≫ i.hom)) ≫ inverse inverses i at h
      simpa only [Category.assoc, hom_inverse, Category.comp_id] using h⟩
    exact ⟨g, Hom.ext rfl⟩

omit [Mono i] in
def composeIso (j : U ⟶ V) : functor i ⋙ functor j ≅ functor (i ≫ j) :=
  NatIso.ofComponents (fun X =>
    { hom := ⟨𝟙 X.base, by
        change 𝟙 X.base ≫ (X.proj ≫ (i.hom ≫ j.hom)) =
          rst (𝟙 X.base) ≫ ((X.proj ≫ i.hom) ≫ j.hom)
        rw [rst_id, Category.id_comp, Category.id_comp, Category.assoc]⟩
      inv := ⟨𝟙 X.base, by
        change 𝟙 X.base ≫ ((X.proj ≫ i.hom) ≫ j.hom) =
          rst (𝟙 X.base) ≫ (X.proj ≫ (i.hom ≫ j.hom))
        rw [rst_id, Category.id_comp, Category.id_comp, Category.assoc]⟩
      hom_inv_id := Hom.ext (Category.id_comp _)
      inv_hom_id := Hom.ext (Category.id_comp _) }) (by
    intro X Y f
    apply Hom.ext
    exact (Category.comp_id f.hom).trans (Category.id_comp f.hom).symm)

end CategoricalEssentialIncompleteness.V46.PartialSlicePostcompose
