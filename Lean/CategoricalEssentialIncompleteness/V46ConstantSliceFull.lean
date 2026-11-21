/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConstantSliceRecursion
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # The full subcategory of constant families and its completion -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ConstantSlice.Full

open RestrictionSubobjects RecursionCategory
variable {R : Type u} [Category.{v} R] [PCategoryStruct R] [PCategory R]
attribute [local instance] SplitObject.productData SplitObject.productLaws SplitObject.productSplits

local instance baseRestriction : RestrictionCategory (SplitObject R) :=
  @PCategory.inducedRestriction (SplitObject R) inferInstance
    SplitObject.productData SplitObject.productLaws

def property (T : SplitObject R) : ObjectProperty (AmbientPartialSlice.Family T) :=
  fun Y => ∃ X : R, family T X = Y

abbrev FullCategory (T : SplitObject R) := (property T).FullSubcategory

def object (T : SplitObject R) (X : R) : FullCategory T := ⟨family T X, ⟨X, rfl⟩⟩

def original {T : SplitObject R} (X : FullCategory T) : R := Classical.choose X.property

def originalIso {T : SplitObject R} (X : FullCategory T) : family T (original X) ≅ X.obj :=
  eqToIso (Classical.choose_spec X.property)

instance restriction (T : SplitObject R) : RestrictionCategory (FullCategory T) where
  rst f := ObjectProperty.homMk (rst f.hom)
  rst_comp_self f := ObjectProperty.hom_ext _ (rst_comp_self f.hom)
  rst_comm f g := ObjectProperty.hom_ext _ (rst_comm f.hom g.hom)
  rst_comp_rst f g := ObjectProperty.hom_ext _ (rst_comp_rst f.hom g.hom)
  rst_comp f g := ObjectProperty.hom_ext _ (rst_comp f.hom g.hom)

def inclusion (T : SplitObject R) : FullCategory T ⥤ AmbientPartialSlice.Family T := (property T).ι

instance inclusion_full (T : SplitObject R) : (inclusion T).Full := ObjectProperty.full_ι _
instance inclusion_faithful (T : SplitObject R) : (inclusion T).Faithful :=
  ObjectProperty.faithful_ι _

theorem inclusion_restriction (T : SplitObject R) : PreservesRestriction (inclusion T) :=
  fun _ => rfl

variable [HasPullbacks (Tot (SplitObject R))]

def product (T : SplitObject R) (X Y : FullCategory T) : FullCategory T :=
  object T (nearProd (original X) (original Y))

def productIso (T : SplitObject R) (X Y : FullCategory T) :
    (inclusion T).obj (product T X Y) ≅
      AmbientSliceProducts.product ((inclusion T).obj X) ((inclusion T).obj Y) :=
  ConstantSlice.productIso (R := R) T (original (R := R) X) (original (R := R) Y) ≪≫
    (AmbientSliceProducts.restrictionProducts T).mapIso (originalIso X) (originalIso Y)

def restrictionProducts (T : SplitObject R) : RestrictionProducts.ProductData (FullCategory T) :=
  FullRestrictionProducts.restrictionProducts (inclusion T) (inclusion_restriction T)
    (AmbientSliceProducts.restrictionProducts T) (product T) (productIso T)

@[instance_reducible] def productData (T : SplitObject R) : PCategoryStruct (FullCategory T) :=
  (restrictionProducts T).pcategoryStruct

theorem productLaws (T : SplitObject R) :
    @PCategory (FullCategory T) inferInstance (productData T) :=
  (restrictionProducts T).pcategoryLaws

theorem productRestriction_eq (T : SplitObject R) :
    @PCategory.inducedRestriction (FullCategory T) inferInstance (productData T) (productLaws T) =
      (inferInstance : RestrictionCategory (FullCategory T)) :=
  (restrictionProducts T).restrictionCategory_eq

variable [HasZeroMorphisms R] [Prodominical R] [Isotype R]
attribute [local instance] SplitObject.prodominicalLaws

local instance baseZero : RestrictionZero (SplitObject R) where
  restrict_zero X Y := by
    change PCategoryStruct.rst (0 : X ⟶ Y) = 0
    exact DomSemilattice.rst_zero X Y

instance ambientZeros (T : SplitObject R) : HasZeroMorphisms (AmbientPartialSlice.Family T) where
  zero X Y := ⟨⟨0, by rw [zero_comp, RestrictionZero.restrict_zero, zero_comp]⟩⟩
  comp_zero := by intros; exact AmbientPartialSlice.Hom.ext comp_zero
  zero_comp := by intros; exact AmbientPartialSlice.Hom.ext zero_comp

instance zeros (T : SplitObject R) : HasZeroMorphisms (FullCategory T) where
  zero _X _Y := ⟨ObjectProperty.homMk 0⟩
  comp_zero := by intros; exact ObjectProperty.hom_ext _ comp_zero
  zero_comp := by intros; exact ObjectProperty.hom_ext _ zero_comp

instance restrictionZero (T : SplitObject R) : RestrictionZero (FullCategory T) where
  restrict_zero _X _Y := ObjectProperty.hom_ext _
    (AmbientPartialSlice.Hom.ext (RestrictionZero.restrict_zero _ _))

instance isotype (T : SplitObject R) : Isotype (FullCategory T) where
  iso X Y := by
    obtain ⟨i⟩ := Isotype.iso (C := R) (original X) (original Y)
    exact ⟨ObjectProperty.isoMk _ ((originalIso X).symm ≪≫
      (ConstantFamilyProducts.constantFunctor T).mapIso ((splittingInclusion (C := R)).mapIso i) ≪≫
        originalIso Y)⟩

omit [Isotype R] in
theorem prodominical (T : SplitObject R) :
    @Prodominical (FullCategory T) inferInstance (productData T) inferInstance :=
  (restrictionProducts T).prodominicalLaws

theorem exists_evaluator (rec : PRecursionCategory R) (T : SplitObject R) :
    ∃ τ : (restrictionProducts T).prod (object T rec.W) (object T rec.W) ⟶ object T rec.W,
      @IsTuringMorphism (FullCategory T) inferInstance (productData T) (productLaws T)
        (object T rec.W) (object T rec.W) (object T rec.W) τ := by
  let Q := (splittingInclusion (C := R)).obj rec.W
  obtain ⟨τ, hτ⟩ := SplitTuring.turingFamily rec Q Q
  let D := AmbientSliceProducts.restrictionProducts T
  let e := AmbientProductTuring.evaluator T τ
  exact ⟨FullRestrictionProducts.evaluator (inclusion T) D (product T) (productIso T)
      (object T rec.W) e,
    FullRestrictionProducts.evaluator_isTuring (inclusion T) (inclusion_restriction T) D
      (product T) (productIso T) (object T rec.W) e
      (AmbientProductTuring.evaluator_isTuring T τ hτ)⟩

@[instance_reducible] def recursionCategory (rec : PRecursionCategory R) (T : SplitObject R) :
    @PRecursionCategory (FullCategory T) inferInstance (productData T) (productLaws T)
      inferInstance (prodominical T) (isotype T) := by
  let : PCategoryStruct (FullCategory T) := productData T
  let : PCategory (FullCategory T) := productLaws T
  let : Prodominical (FullCategory T) := prodominical T
  exact {
    W := object T rec.W
    X := object T rec.W
    Y := object T rec.W
    tau := Classical.choose (exists_evaluator rec T)
    is_turing := Classical.choose_spec (exists_evaluator rec T)
  }

variable (inverses : MonoInverses (SplitObject R)) (T : Tot (SplitObject R))

def actualInclusion : FullCategory T.obj ⥤ PartialMaps.Par (Over T) :=
  inclusion T.obj ⋙ PartialSliceTuring.realization inverses T

instance actualInclusion_full : (actualInclusion inverses T).Full := by
  dsimp only [actualInclusion]
  infer_instance

instance actualInclusion_faithful : (actualInclusion inverses T).Faithful := by
  dsimp only [actualInclusion]
  infer_instance

omit [HasZeroMorphisms R] [Prodominical R] [Isotype R] in
theorem actualInclusion_restriction : PreservesRestriction (actualInclusion inverses T) := by
  intro X Y f
  exact PartialSliceTuring.realization_restriction inverses T f.hom

omit [HasZeroMorphisms R] [Prodominical R] [Isotype R] in
theorem actualInclusion_range (Z : PartialMaps.Par (Over T)) :
    (∃ X : FullCategory T.obj, (actualInclusion inverses T).obj X = Z) ↔
      ∃ X : R, PartialSliceTuring.constantObject T ((splittingInclusion (C := R)).obj X) = Z := by
  constructor
  · rintro ⟨Y, hY⟩
    obtain ⟨X, hX⟩ := Y.property
    refine ⟨X, ?_⟩
    change PartialSliceTuring.realizeObject T (family T.obj X) = Z
    rw [hX]
    exact hY
  · rintro ⟨X, hX⟩
    exact ⟨object T.obj X, hX⟩

def splittingEquivalence (Q : R) : SplitObject (FullCategory T.obj) ≌ PartialMaps.Par (Over T) := by
  letI := PartialSliceSplitting.ambientSplits T.obj
  apply (RestrictionCompletion.equivalence (inclusion T.obj) (inclusion_restriction T.obj) ?_).trans
    (PartialSliceEquivalence.equivalence inverses T).symm
  intro X
  obtain ⟨Y, j, s, hj, hjs, hsj⟩ := ConstantSlice.dense inverses T Q X
  exact ⟨object T.obj Y, j, s, hj, hjs, hsj⟩

omit [HasZeroMorphisms R] [Prodominical R] in
theorem splittingEquivalence_restriction (Q : R) :
    PreservesRestriction (splittingEquivalence inverses T Q).functor := by
  let := PartialSliceSplitting.ambientSplits T.obj
  intro X Y f
  change (PartialSliceEquivalence.equivalence inverses T).inverse.map
      ((RestrictionCompletion.extension (inclusion T.obj)
        (RestrictionCompletion.chosenSplitting (inclusion T.obj)
          (inclusion_restriction T.obj))).map (rst f)) = _
  rw [RestrictionCompletion.extension_restriction (inclusion T.obj) (inclusion_restriction T.obj),
    PartialSliceEquivalence.inverse_preserves_restrictions]
  rfl

omit [HasZeroMorphisms R] [Prodominical R] in
theorem splittingEquivalence_inverse_restriction (Q : R) :
    PreservesRestriction (splittingEquivalence inverses T Q).inverse :=
  RestrictionCompletion.inverse_restriction _ (splittingEquivalence_restriction inverses T Q)

end CategoricalEssentialIncompleteness.V46.ConstantSlice.Full
