/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSlicePostcompose
public import CategoricalEssentialIncompleteness.V46AmbientSliceProducts
public import CategoricalEssentialIncompleteness.V46RestrictionProductCategory
public import PCats.DomProducts

/-! # Pullback reindexing of partial morphisms over a parameter object -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.RestrictionProducts.ProductData

variable {C : Type u} [Category.{v} C] [RestrictionCategory C] (D : ProductData C)

theorem map_restriction {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    D.map (rst f) (rst g) = rst (D.map f g) := by
  have h := @PCategory.rst_nearProd_map C inferInstance D.pcategoryStruct D.pcategoryLaws
    W X Y Z f g
  change @PCategoryStruct.rst C inferInstance D.pcategoryStruct _ _ (D.map f g) =
    D.map (@PCategoryStruct.rst C inferInstance D.pcategoryStruct _ _ f)
      (@PCategoryStruct.rst C inferInstance D.pcategoryStruct _ _ g) at h
  rw [D.restriction_eq, D.restriction_eq, D.restriction_eq] at h
  exact h.symm

theorem map_snd_id {X Y : C} (f : X ⟶ Y) (Z : C) :
    D.map f (𝟙 Z) ≫ D.snd Y Z = rst (D.map f (𝟙 Z)) ≫ D.snd X Z := by
  unfold map
  rw [D.pair_snd, D.pair_restriction]
  simp only [Category.comp_id]
  rw [show rst (D.snd X Z) = 𝟙 _ from D.snd_total X Z, Category.comp_id]

end CategoricalEssentialIncompleteness.V46.RestrictionProducts.ProductData

namespace CategoricalEssentialIncompleteness.V46.PartialSliceReindex

open RestrictionSubobjects AmbientPartialSlice
variable {C : Type u} [Category.{v} C] [RestrictionCategory C] [Splits C]
variable [HasPullbacks (Tot C)] {T U : Tot C} (i : T ⟶ U)

def baseFamily : Family U.obj := ⟨T.obj, i.hom, i.property⟩

def object (X : Family U.obj) : Family T.obj where
  base := (AmbientSliceProducts.product X (baseFamily i)).base
  proj := (AmbientSliceProducts.second X (baseFamily i)).hom
  total := (AmbientPartialSlice.total_iff _).mp (AmbientSliceProducts.second_total _ _)

def first (X : Family U.obj) :
    PartialSlicePostcompose.object i (object i X) ⟶ X :=
  ⟨(AmbientSliceProducts.first X (baseFamily i)).hom, by
    have h := (AmbientSliceProducts.second X (baseFamily i)).over
    change _ ≫ i.hom = _ at h
    rw [show rst (AmbientSliceProducts.second X (baseFamily i)).hom = 𝟙 _ from
      (AmbientPartialSlice.total_iff _).mp (AmbientSliceProducts.second_total _ _),
      Category.id_comp] at h
    change (AmbientSliceProducts.first X (baseFamily i)).hom ≫ X.proj =
      rst (AmbientSliceProducts.first X (baseFamily i)).hom ≫
        ((AmbientSliceProducts.second X (baseFamily i)).hom ≫ i.hom)
    rw [show rst (AmbientSliceProducts.first X (baseFamily i)).hom = 𝟙 _ from
      (AmbientPartialSlice.total_iff _).mp (AmbientSliceProducts.first_total _ _), Category.id_comp]
    exact h.symm⟩

def map {X Y : Family U.obj} (f : X ⟶ Y) : object i X ⟶ object i Y :=
  ⟨((AmbientSliceProducts.restrictionProducts U.obj).map f (𝟙 (baseFamily i))).hom, by
    let D := AmbientSliceProducts.restrictionProducts U.obj
    exact congrArg (fun k : D.prod X (baseFamily i) ⟶ baseFamily i => k.hom)
      (D.map_snd_id f (baseFamily i))⟩

def functor : Family U.obj ⥤ Family T.obj where
  obj := object i
  map := map i
  map_id X := by
    apply Hom.ext
    exact congrArg (fun k : AmbientSliceProducts.product X (baseFamily i) ⟶
      AmbientSliceProducts.product X (baseFamily i) => k.hom)
      ((AmbientSliceProducts.restrictionProducts U.obj).map_id X (baseFamily i))
  map_comp {X Y Z} f g := by
    apply Hom.ext
    change ((AmbientSliceProducts.restrictionProducts U.obj).map (f ≫ g)
      (𝟙 (baseFamily i))).hom =
        ((AmbientSliceProducts.restrictionProducts U.obj).map f (𝟙 (baseFamily i)) ≫
          (AmbientSliceProducts.restrictionProducts U.obj).map g (𝟙 (baseFamily i))).hom
    have h := congrArg (fun k : AmbientSliceProducts.product X (baseFamily i) ⟶
      AmbientSliceProducts.product Z (baseFamily i) => k.hom)
      ((AmbientSliceProducts.restrictionProducts U.obj).map_comp
      f g (𝟙 (baseFamily i)) (𝟙 (baseFamily i)))
    simpa only [Category.id_comp] using h.symm

theorem map_first {X Y : Family U.obj} (f : X ⟶ Y) :
    (map i f).hom ≫ (first i Y).hom = (first i X).hom ≫ f.hom :=
  congrArg (fun k : AmbientSliceProducts.product X (baseFamily i) ⟶ Y => k.hom)
    ((AmbientSliceProducts.restrictionProducts U.obj).map_fst_of_total
    f (𝟙 (baseFamily i)) (rst_id _))

omit [Splits C] in
theorem first_total (X : Family U.obj) : isTotal (first i X) :=
  (AmbientPartialSlice.total_iff (first i X)).mpr
    ((AmbientPartialSlice.total_iff (AmbientSliceProducts.first X (baseFamily i))).mp
      (AmbientSliceProducts.first_total _ _))

theorem hom_ext {X : Family T.obj} {Y : Family U.obj} {f g : X ⟶ object i Y}
    (h : f.hom ≫ (first i Y).hom = g.hom ≫ (first i Y).hom) : f = g := by
  have hd : rst f.hom = rst g.hom := by
    have ht := (AmbientPartialSlice.total_iff _).mp (first_total i Y)
    simpa only [rst_comp_of_isTotal _ ht] using congrArg rst h
  apply Hom.ext
  apply AmbientSliceProducts.partial_pullback_hom_ext
    (IsPullback.of_hasPullback (AmbientSliceProducts.totalProjection Y)
      (AmbientSliceProducts.totalProjection (baseFamily i)))
  · exact h
  · change f.hom ≫ (object i Y).proj = g.hom ≫ (object i Y).proj
    rw [f.over, g.over, hd]

theorem preserves_restriction : PreservesRestriction (functor i) := by
  intro X Y f
  apply Hom.ext
  change ((AmbientSliceProducts.restrictionProducts U.obj).map (rst f)
      (𝟙 (baseFamily i))).hom =
    (rst ((AmbientSliceProducts.restrictionProducts U.obj).map f (𝟙 (baseFamily i)))).hom
  have h := congrArg (fun k : AmbientSliceProducts.product X (baseFamily i) ⟶
    AmbientSliceProducts.product X (baseFamily i) => k.hom)
    ((AmbientSliceProducts.restrictionProducts U.obj).map_restriction
    f (𝟙 (baseFamily i)))
  simpa only [rst_id] using h

end CategoricalEssentialIncompleteness.V46.PartialSliceReindex
