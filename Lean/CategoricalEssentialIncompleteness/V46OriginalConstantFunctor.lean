/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ConstantSliceFull
public import CategoricalEssentialIncompleteness.V46AssociatedEvaluation

/-! # The original constant-family functor and its specified evaluator -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.OriginalConstantFunctor
open RestrictionSubobjects RecursionCategory
variable {R : Type u} [Category.{v} R] [PCategoryStruct R] [PCategory R]
attribute [local instance] SplitObject.productData SplitObject.productLaws SplitObject.productSplits
local instance baseRestriction : RestrictionCategory (SplitObject R) := PCategory.inducedRestriction

/-- The literal full subcategory contains precisely the original constant
objects, and this functor sends a morphism to its product with the identity. -/
def functor (T : SplitObject R) : R ⥤ ConstantSlice.Full.FullCategory T where
  obj := ConstantSlice.Full.object T
  map f := ObjectProperty.homMk
    ((ConstantFamilyProducts.constantFunctor T).map ((splittingInclusion (C := R)).map f))
  map_id X := ObjectProperty.hom_ext _ (by
    change (ConstantFamilyProducts.constantFunctor T).map
      ((splittingInclusion (C := R)).map (𝟙 X)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id])
  map_comp f g := ObjectProperty.hom_ext _ (by
    change (ConstantFamilyProducts.constantFunctor T).map
      ((splittingInclusion (C := R)).map (f ≫ g)) = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    rfl)

theorem map_value (T : SplitObject R) {X Y : R} (f : X ⟶ Y) :
    ((functor T).map f).hom.hom =
      nearProd_map (𝟙 T) ((splittingInclusion (C := R)).map f) := rfl

variable [HasPullbacks (Tot (SplitObject R))]

/-- The common logical point supplies faithfulness of this exact functor. -/
theorem faithful (inverses : MonoInverses (SplitObject R)) {Z T : Tot (SplitObject R)}
    (point : Z ⟶ T) (hZ : IsTerminal Z) : (functor T.obj).Faithful := by
  let K := PartialSliceTheoryFamilies.constantFunctor inverses T
  have hK := AssociatedCategory.constant_faithful inverses point hZ
  refine ⟨fun {X Y} f g h => ?_⟩
  have hi : (splittingInclusion (C := R)).map f = (splittingInclusion (C := R)).map g := by
    apply hK.map_injective
    exact congrArg (fun k => (PartialSliceTuring.realization inverses T).map k.hom) h
  exact congrArg SplitObject.Hom.hom hi

/-- The product comparison accounts for the full subcategory's chosen
representatives of its objects. -/
def productComparison (T : SplitObject R) (X Y : R) :
    ConstantSlice.Full.product T ((functor T).obj X) ((functor T).obj Y) ≅
      (functor T).obj (nearProd X Y) :=
  (ConstantSlice.Full.inclusion T).preimageIso
    (ConstantSlice.Full.productIso T _ _ ≪≫ (ConstantSlice.productIso T X Y).symm)

/-- Under the canonical product comparison, this is the image of the
specified source evaluator, with no choice of a replacement evaluator. -/
def evaluator (T : SplitObject R) {Q : R} (τ : nearProd Q Q ⟶ Q) :
    ConstantSlice.Full.product T ((functor T).obj Q) ((functor T).obj Q) ⟶
      (functor T).obj Q := (productComparison T Q Q).hom ≫ (functor T).map τ

omit [HasPullbacks (Tot (SplitObject R))] in
theorem eqToHom_base {X Y : SplitObject R} (h : X = Y) :
    (eqToHom h).hom = X.domain.hom ≫ eqToHom (congrArg SplitObject.base h) := by
  subst Y
  simp only [eqToHom_refl, Category.comp_id]
  rfl

omit [HasPullbacks (Tot (SplitObject R))] in
theorem split_evaluator {Q : R} (τ : nearProd Q Q ⟶ Q) :
    (ConstantSlice.fullProductIso Q Q).inv ≫
      SplitTuring.evaluator ((splittingInclusion (C := R)).obj Q)
        ((splittingInclusion (C := R)).obj Q) τ =
      (splittingInclusion (C := R)).map τ := by
  apply SplitObject.Hom.ext
  change (ConstantSlice.fullProductIso Q Q).inv.hom ≫
    (nearProd_map (𝟙 Q) (𝟙 Q) ≫ τ ≫ 𝟙 Q) = τ
  have h0 : (ConstantSlice.fullProductIso Q Q).inv.hom = 𝟙 (nearProd Q Q) := by
    have h : SplitObject.binaryProduct ((splittingInclusion (C := R)).obj Q)
        ((splittingInclusion (C := R)).obj Q) =
        (splittingInclusion (C := R)).obj (nearProd Q Q) := by
      unfold SplitObject.binaryProduct splittingInclusion
      congr 1
      exact Idem.ext (PCategory.nearProd_id Q Q)
    change (eqToHom h.symm).hom = _
    rw [eqToHom_base]
    change 𝟙 (nearProd Q Q) ≫ eqToHom _ = _
    simp only [eqToHom_refl, Category.id_comp]
  erw [h0, PCategory.nearProd_id, Category.id_comp, Category.comp_id, Category.id_comp]

/-- The constant-family and ambient-product comparisons cancel. -/
theorem ambient_evaluator (T : SplitObject R) {Q : R} (τ : nearProd Q Q ⟶ Q) :
    (ConstantSlice.productIso T Q Q).hom ≫
      AmbientProductTuring.evaluator T
        (SplitTuring.evaluator ((splittingInclusion (C := R)).obj Q)
          ((splittingInclusion (C := R)).obj Q) τ) =
      ((functor T).map τ).hom := by
  unfold ConstantSlice.productIso ConstantFamilyProducts.productIso
    AmbientProductTuring.evaluator AmbientProductTuring.productIso
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, ← Category.assoc]
  rw [show ((ConstantFamilyProducts.fixedProduct T _ _).iso
      ((AmbientSliceProducts.restrictionProducts T).binary _ _)).hom =
      (((AmbientSliceProducts.restrictionProducts T).binary _ _).iso
        (AmbientProductTuring.fixedProduct T _ _)).inv from rfl]
  rw [Category.assoc, ← Category.assoc _ _ (AmbientSliceTuring.evaluator T _),
    Iso.inv_hom_id, Category.id_comp]
  change ((ConstantFamilyProducts.constantFunctor T).map
      (ConstantSlice.fullProductIso Q Q).inv ≫
      (ConstantFamilyProducts.associatorIso T _ _).inv) ≫
      ((ConstantFamilyProducts.associatorIso T _ _).hom ≫
        (ConstantFamilyProducts.constantFunctor T).map
          (SplitTuring.evaluator ((splittingInclusion (C := R)).obj Q)
            ((splittingInclusion (C := R)).obj Q) τ)) = _
  rw [Category.assoc, ← Category.assoc (ConstantFamilyProducts.associatorIso T _ _).inv,
    Iso.inv_hom_id, Category.id_comp, ← CategoryTheory.Functor.map_comp, split_evaluator]
  rfl

theorem evaluator_isTuring (T : SplitObject R) {Q : R} (τ : nearProd Q Q ⟶ Q)
    (hτ : IsTuringMorphism τ) :
    @IsTuringMorphism (ConstantSlice.Full.FullCategory T) inferInstance
      (ConstantSlice.Full.productData T) (ConstantSlice.Full.productLaws T)
      ((functor T).obj Q) ((functor T).obj Q) ((functor T).obj Q) (evaluator T τ) := by
  let F := ConstantSlice.Full.inclusion T
  let D := AmbientSliceProducts.restrictionProducts T
  let e := AmbientProductTuring.evaluator T
    (SplitTuring.evaluator ((splittingInclusion (C := R)).obj Q)
      ((splittingInclusion (C := R)).obj Q) τ)
  have he := AmbientProductTuring.evaluator_isTuring T _
    (SplitTuring.evaluator_isTuring _ _ τ hτ)
  have hh := FullRestrictionProducts.evaluator_isTuring F
    (ConstantSlice.Full.inclusion_restriction T) D
    (ConstantSlice.Full.product T) (ConstantSlice.Full.productIso T) ((functor T).obj Q) e he
  have hEq : evaluator T τ = FullRestrictionProducts.evaluator F D
      (ConstantSlice.Full.product T) (ConstantSlice.Full.productIso T) ((functor T).obj Q) e := by
    apply F.map_injective
    change F.map ((productComparison T Q Q).hom ≫ (functor T).map τ) =
      F.map (F.preimage (_ ≫ e))
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_preimage]
    have hp : F.map (productComparison T Q Q).hom =
        (ConstantSlice.Full.productIso T ((functor T).obj Q) ((functor T).obj Q)).hom ≫
          (ConstantSlice.productIso T Q Q).inv := by
      exact F.map_preimage _
    rw [hp, Category.assoc]
    change _ ≫ ((ConstantSlice.productIso T Q Q).inv ≫ ((functor T).map τ).hom) = _
    erw [← ambient_evaluator T τ,
      ← Category.assoc (ConstantSlice.productIso T Q Q).inv,
      Iso.inv_hom_id, Category.id_comp]
  rw [hEq]
  exact hh

end CategoricalEssentialIncompleteness.V46.OriginalConstantFunctor
