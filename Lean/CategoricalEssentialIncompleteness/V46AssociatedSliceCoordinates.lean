/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46AssociatedIncompleteness
public import PCats.DomTotalEmbedding
public import CategoricalEssentialIncompleteness.V46PartialSliceTheorySubobjects

/-! # Chosen-product coordinates of the associated constant-family functor -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.AssociatedSliceCoordinates
open RestrictionSubobjects

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [Regular (Tot C)]

def nearProductLimit (U X : Tot C) :
    IsLimit (BinaryFan.mk (TotalSubcategory.binaryProductFst U X)
      (TotalSubcategory.binaryProductSnd U X)) :=
  BinaryFan.isLimitMk
    (fun t => TotalSubcategory.binaryProductLift t.fst t.snd)
    (fun t => TotalSubcategory.binaryProductLift_fst t.fst t.snd)
    (fun t => TotalSubcategory.binaryProductLift_snd t.fst t.snd)
    (fun _ m hf hg => TotalSubcategory.binaryProductLift_unique m hf hg)

def productIso (U X : Tot C) : U ⨯ X ≅ TotalSubcategory.binaryProduct U X :=
  (prodIsProd U X).conePointUniqueUpToIso (nearProductLimit U X)

omit [Splits C] in
@[reassoc] theorem productIso_fst (U X : Tot C) :
    (productIso U X).hom ≫ TotalSubcategory.binaryProductFst U X = prod.fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp (prodIsProd U X) (nearProductLimit U X) ⟨.left⟩

omit [Splits C] in
@[reassoc] theorem productIso_snd (U X : Tot C) :
    (productIso U X).hom ≫ TotalSubcategory.binaryProductSnd U X = prod.snd :=
  IsLimit.conePointUniqueUpToIso_hom_comp (prodIsProd U X) (nearProductLimit U X) ⟨.right⟩

/-- The restriction-product family underlying the existing partial functor. -/
def actualConstant (U : Tot C) : Tot C ⥤ Over U where
  obj X := (PartialSliceTuring.constantObject U X.obj).obj
  map {X Y} f := Over.homMk
    (⟨PCategoryStruct.nearProd_map (𝟙 U.obj) f.hom,
      PCategory.isTotal_nearProd_map (rst_id U.obj) f.property⟩ :
        TotalSubcategory.binaryProduct U X ⟶ TotalSubcategory.binaryProduct U Y) (by
          apply WideSubcategory.hom_ext
          change PCategoryStruct.nearProd_map (𝟙 U.obj) f.hom ≫
            PCategoryStruct.p0 U.obj Y.obj = PCategoryStruct.p0 U.obj X.obj
          simpa only [Category.comp_id] using PCategory.p0_nat_of_isTotal (𝟙 U.obj) f.property)
  map_id X := by
    apply Over.OverMorphism.ext
    apply WideSubcategory.hom_ext
    exact PCategory.nearProd_id U.obj X.obj
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply WideSubcategory.hom_ext
    change PCategoryStruct.nearProd_map (𝟙 U.obj) (f.hom ≫ g.hom) =
      PCategoryStruct.nearProd_map (𝟙 U.obj) f.hom ≫
        PCategoryStruct.nearProd_map (𝟙 U.obj) g.hom
    rw [PCategory.nearProd_comp, Category.id_comp]

def component (U X : Tot C) : constantFamily U X ≅ (actualConstant U).obj X :=
  Over.isoMk (productIso U X) (productIso_fst U X)

def comparison (U : Tot C) : constantFamilyFunctor U ≅ actualConstant U :=
  NatIso.ofComponents (component U) (by
    intro X Y f
    apply Over.OverMorphism.ext
    apply (nearProductLimit U Y).hom_ext
    rintro ⟨j⟩
    cases j
    · change (prod.map (𝟙 U) f ≫ (productIso U Y).hom) ≫
          TotalSubcategory.binaryProductFst U Y =
        ((productIso U X).hom ≫ ((actualConstant U).map f).left) ≫
          TotalSubcategory.binaryProductFst U Y
      rw [Category.assoc, productIso_fst, prod.map_fst, Category.comp_id]
      have hp : ((actualConstant U).map f).left ≫ TotalSubcategory.binaryProductFst U Y =
          TotalSubcategory.binaryProductFst U X := by
        apply WideSubcategory.hom_ext
        change PCategoryStruct.nearProd_map (𝟙 U.obj) f.hom ≫
          PCategoryStruct.p0 U.obj Y.obj = PCategoryStruct.p0 U.obj X.obj
        simpa only [Category.comp_id] using PCategory.p0_nat_of_isTotal (𝟙 U.obj) f.property
      rw [Category.assoc, hp, productIso_fst]
    · change (prod.map (𝟙 U) f ≫ (productIso U Y).hom) ≫
          TotalSubcategory.binaryProductSnd U Y =
        ((productIso U X).hom ≫ ((actualConstant U).map f).left) ≫
          TotalSubcategory.binaryProductSnd U Y
      rw [Category.assoc, productIso_snd, prod.map_snd, Category.assoc]
      have hp : ((actualConstant U).map f).left ≫ TotalSubcategory.binaryProductSnd U Y =
          TotalSubcategory.binaryProductSnd U X ≫ f := by
        apply WideSubcategory.hom_ext
        exact PCategory.p1_nat_of_isTotal f.hom (rst_id U.obj)
      rw [hp, ← Category.assoc, productIso_snd])

local instance coordinateSliceRegular (U : Tot C) : Regular (Over U) := RegularSlices.regular U
local instance coordinateConstantLimits (U : Tot C) :
    PreservesFiniteLimits (constantFamilyFunctor U) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits U
local instance coordinateActualLimits (U : Tot C) : PreservesFiniteLimits (actualConstant U) :=
  preservesFiniteLimits_of_natIso (comparison U)

omit [Splits C] in
/-- The transported theorem subobject is the theorem family of the partial functor, in its
restriction-product coordinates. -/
theorem theory_value (U : Tot C) {S : Tot C} (T : Subobject S) :
    (Subobject.map ((comparison U).hom.app S)).obj
        (FiniteLimitSubobjects.object (constantFamilyFunctor U) T) =
      FiniteLimitSubobjects.object (actualConstant U) T := by
  rw [FiniteLimitSubobjects.object, FiniteLimitSubobjects.object, Subobject.map_mk]
  apply Subobject.mk_eq_mk_of_comm _ _ ((comparison U).app (T : Tot C))
  exact ((comparison U).hom.naturality T.arrow).symm

theorem actual_map (inverses : MonoInverses C) (U : Tot C) {X Y : Tot C} (f : X ⟶ Y) :
    (PartialSliceTheoryFamilies.constantFunctor inverses U).map f.hom =
      PartialMaps.ofTotal ((actualConstant U).map f) := by
  apply (PartialSliceEquivalence.functor inverses U).map_injective
  rw [PartialSliceTheoryFamilies.constant_value]
  apply AmbientPartialSlice.Hom.ext
  rw [PartialSliceChangeBase.value_ofTotal]
  rfl

theorem evaluation_total (inverses : MonoInverses C) {Z U : Tot C} (point : Z ⟶ U)
    {X Y : PartialMaps.Par (Over U)} (f : X.obj ⟶ Y.obj) :
    (AssociatedCategory.evaluation inverses point).map (PartialMaps.ofTotal f) =
      (((Over.pullback point).map f).left).hom := by
  have h := congrArg (fun g => ((PartialSliceEquivalence.functor inverses Z).map g).hom)
    (PartialSliceChangeBase.reindex_ofTotal point inverses f)
  rw [PartialSliceChangeBase.reindex_value, PartialSliceChangeBase.value_ofTotal] at h
  exact h

end CategoricalEssentialIncompleteness.V46.AssociatedSliceCoordinates
