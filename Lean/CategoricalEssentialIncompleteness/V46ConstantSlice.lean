/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConstantFamilyProducts
public import CategoricalEssentialIncompleteness.V46FullRestrictionProducts
public import CategoricalEssentialIncompleteness.V46RestrictionCompletion
public import CategoricalEssentialIncompleteness.V46PartialSliceSplitting
public import CategoricalEssentialIncompleteness.V46PartialSliceRetractions
public import CategoricalEssentialIncompleteness.V46PartialSliceRealization
public import Mathlib.CategoryTheory.InducedCategory

/-! # The full restriction subcategory of original constant families -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ConstantSlice

open RestrictionSubobjects RecursionCategory
variable {R : Type u} [Category.{v} R] [PCategoryStruct R] [PCategory R]
attribute [local instance] SplitObject.productData SplitObject.productLaws SplitObject.productSplits

local instance baseRestriction : RestrictionCategory (SplitObject R) :=
  @PCategory.inducedRestriction (SplitObject R) inferInstance
    SplitObject.productData SplitObject.productLaws

def family (T : SplitObject R) (X : R) : AmbientPartialSlice.Family T :=
  AmbientSliceTuring.constantFamily T ((splittingInclusion (C := R)).obj X)

/-- Objects are indexed by original R; every partial over-T morphism between
their constant families is a morphism here. -/
abbrev ConstantCategory (T : SplitObject R) :=
  InducedCategory (AmbientPartialSlice.Family T) (family T)

instance restriction (T : SplitObject R) : RestrictionCategory (ConstantCategory T) where
  rst f := InducedCategory.homMk (rst f.hom)
  rst_comp_self f := InducedCategory.hom_ext (rst_comp_self f.hom)
  rst_comm f g := InducedCategory.hom_ext (rst_comm f.hom g.hom)
  rst_comp_rst f g := InducedCategory.hom_ext (rst_comp_rst f.hom g.hom)
  rst_comp f g := InducedCategory.hom_ext (rst_comp f.hom g.hom)

def inclusion (T : SplitObject R) : ConstantCategory T ⥤ AmbientPartialSlice.Family T :=
  inducedFunctor (family T)

instance inclusion_full (T : SplitObject R) : (inclusion T).Full := InducedCategory.full _
instance inclusion_faithful (T : SplitObject R) : (inclusion T).Faithful :=
  InducedCategory.faithful _

theorem inclusion_restriction (T : SplitObject R) : PreservesRestriction (inclusion T) :=
  fun _ => rfl

def fullProductIso (X Y : R) :
    SplitObject.binaryProduct ((splittingInclusion (C := R)).obj X)
      ((splittingInclusion (C := R)).obj Y) ≅
        (splittingInclusion (C := R)).obj (nearProd X Y) := by
  have he : SplitObject.binaryProduct ((splittingInclusion (C := R)).obj X)
      ((splittingInclusion (C := R)).obj Y) =
        (splittingInclusion (C := R)).obj (nearProd X Y) := by
    unfold SplitObject.binaryProduct splittingInclusion
    congr 1
    exact Idem.ext (PCategory.nearProd_id X Y)
  exact eqToIso he

variable [HasPullbacks (Tot (SplitObject R))]

def productIso (T : SplitObject R) (X Y : ConstantCategory T) :
    (inclusion T).obj (nearProd X Y : R) ≅
      AmbientSliceProducts.product ((inclusion T).obj X) ((inclusion T).obj Y) :=
  (ConstantFamilyProducts.constantFunctor T).mapIso (fullProductIso (R := R) X Y).symm ≪≫
    ConstantFamilyProducts.productIso T ((splittingInclusion (C := R)).obj X)
      ((splittingInclusion (C := R)).obj Y)

def restrictionProducts (T : SplitObject R) :
    RestrictionProducts.ProductData (ConstantCategory T) :=
  FullRestrictionProducts.restrictionProducts (inclusion T) (inclusion_restriction T)
    (AmbientSliceProducts.restrictionProducts T) (fun X Y => (nearProd X Y : R)) (productIso T)

@[instance_reducible] def productData (T : SplitObject R) : PCategoryStruct (ConstantCategory T) :=
  (restrictionProducts T).pcategoryStruct

theorem productLaws (T : SplitObject R) :
    @PCategory (ConstantCategory T) inferInstance (productData T) :=
  (restrictionProducts T).pcategoryLaws

theorem productRestriction_eq (T : SplitObject R) :
    @PCategory.inducedRestriction (ConstantCategory T) inferInstance
      (productData T) (productLaws T) =
      (inferInstance : RestrictionCategory (ConstantCategory T)) :=
  (restrictionProducts T).restrictionCategory_eq

variable [Isotype R]

instance isotype (T : SplitObject R) : Isotype (ConstantCategory T) where
  iso X Y := by
    obtain ⟨i⟩ := Isotype.iso (C := R) X Y
    exact ⟨InducedCategory.isoMk ((ConstantFamilyProducts.constantFunctor T).mapIso
      ((splittingInclusion (C := R)).mapIso i))⟩

variable (inverses : MonoInverses (SplitObject R)) (T : Tot (SplitObject R))

def actualInclusion : ConstantCategory T.obj ⥤ PartialMaps.Par (Over T) :=
  inclusion T.obj ⋙ PartialSliceTuring.realization inverses T

instance actualInclusion_full : (actualInclusion inverses T).Full := by
  dsimp only [actualInclusion]
  infer_instance

instance actualInclusion_faithful : (actualInclusion inverses T).Faithful := by
  dsimp only [actualInclusion]
  infer_instance

omit [Isotype R] in
theorem actualInclusion_restriction : PreservesRestriction (actualInclusion inverses T) := by
  intro X Y f
  exact PartialSliceTuring.realization_restriction inverses T f.hom

omit [Isotype R] in
theorem actualInclusion_object (X : ConstantCategory T.obj) :
    (actualInclusion inverses T).obj X =
      PartialSliceTuring.constantObject T ((splittingInclusion (C := R)).obj X) := rfl

omit [HasPullbacks (Tot (SplitObject R))] in
include inverses in
theorem dense (Q : R) (X : AmbientPartialSlice.Family T.obj) :
    ∃ (Y : ConstantCategory T.obj) (j : X ⟶ (inclusion T.obj).obj Y)
      (s : (inclusion T.obj).obj Y ⟶ X),
      isTotal j ∧ j ≫ s = 𝟙 X ∧ s ≫ j = rst s := by
  obtain ⟨m, r, hm, hmr⟩ := SplitTuring.exists_total_retract Q X.base
  have hm' : isTotal m := by
    change @PCategoryStruct.rst (SplitObject R) inferInstance SplitObject.productData _ _ m = _
    rw [SplitObject.productData_restriction]
    exact hm
  obtain ⟨j, s, hj, hj0, hjs, hsj, hs0⟩ := SliceTuringParameters.total_retract_over
    inverses X.proj X.total m hm' r hmr
  let j' : X ⟶ (inclusion T.obj).obj (Q : ConstantCategory T.obj) := ⟨j, by
    change j ≫ p0 T.obj _ = CategoryTheory.RestrictionCategory.rst j ≫ X.proj
    rw [hj0, hj, Category.id_comp]⟩
  let s' : (inclusion T.obj).obj (Q : ConstantCategory T.obj) ⟶ X := ⟨s, hs0⟩
  exact ⟨Q, j', s', (AmbientPartialSlice.total_iff j').mpr hj,
    AmbientPartialSlice.Hom.ext hjs, AmbientPartialSlice.Hom.ext hsj⟩

def splittingEquivalence (Q : R) :
    SplitObject (ConstantCategory T.obj) ≌ PartialMaps.Par (Over T) := by
  letI := PartialSliceSplitting.ambientSplits T.obj
  exact RestrictionCompletion.equivalence (inclusion T.obj) (inclusion_restriction T.obj)
    (dense inverses T Q) |>.trans (PartialSliceEquivalence.equivalence inverses T).symm

end CategoricalEssentialIncompleteness.V46.ConstantSlice
