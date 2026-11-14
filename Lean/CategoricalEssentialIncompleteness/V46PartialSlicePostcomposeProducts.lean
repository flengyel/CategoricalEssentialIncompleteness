/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSliceAdjunctions
public import CategoricalEssentialIncompleteness.V46PartialSliceProducts
public import CategoricalEssentialIncompleteness.V46ConstantFamilyProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-! # Postcomposition along a mono preserves binary restriction products -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialSlicePostcomposeProducts

open RestrictionSubobjects AmbientPartialSlice AmbientSliceProducts
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [HasPullbacks (Tot C)] {T U : Tot C} (i : T ⟶ U) [Mono i]

omit [Splits C] in
theorem productPullback (X Y : Family T.obj) :
    IsPullback (pullback.fst (totalProjection X) (totalProjection Y))
      (pullback.snd (totalProjection X) (totalProjection Y))
      (totalProjection X ≫ i) (totalProjection Y ≫ i) :=
  IsPullback.of_isLimit (pullbackIsPullbackOfCompMono (totalProjection X) (totalProjection Y) i)

def baseIso (X Y : Family T.obj) :
    (product X Y).base ≅
      (product (PartialSlicePostcompose.object i X) (PartialSlicePostcompose.object i Y)).base where
  hom := (productPullback i X Y).isoPullback.hom.hom
  inv := (productPullback i X Y).isoPullback.inv.hom
  hom_inv_id := congrArg (fun k => k.hom) (productPullback i X Y).isoPullback.hom_inv_id
  inv_hom_id := congrArg (fun k => k.hom) (productPullback i X Y).isoPullback.inv_hom_id

omit [Splits C] in
theorem baseIso_fst (X Y : Family T.obj) :
    (baseIso i X Y).hom ≫
        (first (PartialSlicePostcompose.object i X) (PartialSlicePostcompose.object i Y)).hom =
      (first X Y).hom :=
  congrArg (fun k : pullback (totalProjection X) (totalProjection Y) ⟶ (⟨X.base⟩ : Tot C) => k.hom)
    (productPullback i X Y).isoPullback_hom_fst

omit [Splits C] in
theorem baseIso_snd (X Y : Family T.obj) :
    (baseIso i X Y).hom ≫
        (second (PartialSlicePostcompose.object i X) (PartialSlicePostcompose.object i Y)).hom =
      (second X Y).hom :=
  congrArg (fun k : pullback (totalProjection X) (totalProjection Y) ⟶ (⟨Y.base⟩ : Tot C) => k.hom)
    (productPullback i X Y).isoPullback_hom_snd

def ambientProductIso (X Y : Family T.obj) :
    PartialSlicePostcompose.object i (product X Y) ≅
      product (PartialSlicePostcompose.object i X) (PartialSlicePostcompose.object i Y) :=
  ConstantFamilyProducts.familyIso _ _ (baseIso i X Y) (by
    change (baseIso i X Y).hom ≫
        ((first (PartialSlicePostcompose.object i X) (PartialSlicePostcompose.object i Y)).hom ≫
          (X.proj ≫ i.hom)) = ((first X Y).hom ≫ X.proj) ≫ i.hom
    rw [← Category.assoc, baseIso_fst, Category.assoc])

omit [Splits C] in
theorem ambientProductIso_fst (X Y : Family T.obj) :
    (ambientProductIso i X Y).hom ≫
        first (PartialSlicePostcompose.object i X) (PartialSlicePostcompose.object i Y) =
      (PartialSlicePostcompose.functor i).map (first X Y) := Hom.ext (baseIso_fst i X Y)

omit [Splits C] in
theorem ambientProductIso_snd (X Y : Family T.obj) :
    (ambientProductIso i X Y).hom ≫
        second (PartialSlicePostcompose.object i X) (PartialSlicePostcompose.object i Y) =
      (PartialSlicePostcompose.functor i).map (second X Y) := Hom.ext (baseIso_snd i X Y)

variable (inverses : MonoInverses C)

def actualProductIso (X Y : PartialMaps.Par (Over T)) :
    (PartialSliceChangeBase.postcompose i).obj (PartialSliceProducts.product inverses T X Y) ≅
      PartialSliceProducts.product inverses U
        ((PartialSliceChangeBase.postcompose i).obj X)
        ((PartialSliceChangeBase.postcompose i).obj Y) :=
  (PartialSliceEquivalence.functor inverses U).preimageIso
    (X := (PartialSliceChangeBase.postcompose i).obj (PartialSliceProducts.product inverses T X Y))
    (Y := PartialSliceProducts.product inverses U
      ((PartialSliceChangeBase.postcompose i).obj X) ((PartialSliceChangeBase.postcompose i).obj Y))
    (ambientProductIso i ((PartialSliceEquivalence.functor inverses T).obj X)
      ((PartialSliceEquivalence.functor inverses T).obj Y))

theorem actualProductIso_value (X Y : PartialMaps.Par (Over T)) :
    (PartialSliceEquivalence.functor inverses U).map (actualProductIso i inverses X Y).hom =
      (ambientProductIso i ((PartialSliceEquivalence.functor inverses T).obj X)
        ((PartialSliceEquivalence.functor inverses T).obj Y)).hom :=
  (PartialSliceEquivalence.functor inverses U).map_preimage _

theorem actualProductIso_fst (X Y : PartialMaps.Par (Over T)) :
    (actualProductIso i inverses X Y).hom ≫
        PartialSliceProducts.first inverses U
          ((PartialSliceChangeBase.postcompose i).obj X)
          ((PartialSliceChangeBase.postcompose i).obj Y) =
      (PartialSliceChangeBase.postcompose i).map (PartialSliceProducts.first inverses T X Y) := by
  apply (PartialSliceEquivalence.functor inverses U).map_injective
  rw [CategoryTheory.Functor.map_comp, actualProductIso_value,
    PartialSliceProducts.first_value, PartialSliceChangeBase.postcompose_value,
    PartialSliceProducts.first_value]
  exact ambientProductIso_fst i _ _

theorem actualProductIso_snd (X Y : PartialMaps.Par (Over T)) :
    (actualProductIso i inverses X Y).hom ≫
        PartialSliceProducts.second inverses U
          ((PartialSliceChangeBase.postcompose i).obj X)
          ((PartialSliceChangeBase.postcompose i).obj Y) =
      (PartialSliceChangeBase.postcompose i).map (PartialSliceProducts.second inverses T X Y) := by
  apply (PartialSliceEquivalence.functor inverses U).map_injective
  rw [CategoryTheory.Functor.map_comp, actualProductIso_value,
    PartialSliceProducts.second_value, PartialSliceChangeBase.postcompose_value,
    PartialSliceProducts.second_value]
  exact ambientProductIso_snd i _ _

end CategoricalEssentialIncompleteness.V46.PartialSlicePostcomposeProducts
