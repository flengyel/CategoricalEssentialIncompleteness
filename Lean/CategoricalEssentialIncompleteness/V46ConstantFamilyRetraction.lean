/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSliceTheoryComparison
public import CategoricalEssentialIncompleteness.V46RestrictionTerminal

/-! # Constant families, terminal products and evaluation at a global point -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ConstantFamilyRetraction

open RestrictionSubobjects AmbientPartialSlice
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable {Z : Tot C} (hZ : IsTerminal Z)

def terminalProductIso (X : C) : nearProd Z.obj X ≅ X where
  hom := p1 Z.obj X
  inv := partialPairing (RestrictionTerminal.terminate hZ X) (𝟙 X)
  hom_inv_id := by
    rw [PCategory.comp_partialPairing, Category.comp_id]
    have h : p1 Z.obj X ≫ RestrictionTerminal.terminate hZ X = p0 Z.obj X :=
      (RestrictionTerminal.terminate_unique hZ _
        (isTotal_comp (PCategory.p1_isTotal _ _) (RestrictionTerminal.terminate_total hZ X))).trans
      (RestrictionTerminal.terminate_unique hZ _ (PCategory.p0_isTotal _ _)).symm
    rw [h, PCategory.partialPairing_p0_p1]
  inv_hom_id := by
    rw [PCategory.p1_partialPairing]
    change CategoryTheory.RestrictionCategory.rst
      (RestrictionTerminal.terminate hZ X) ≫ 𝟙 X = 𝟙 X
    rw [RestrictionTerminal.terminate_total, Category.id_comp]

def constantTerminalIso :
    ConstantFamilyProducts.constantFunctor Z.obj ⋙ AmbientPartialSlice.forget ≅ 𝟭 C :=
  NatIso.ofComponents (terminalProductIso hZ) (fun f => PCategory.p1_nat f)

variable [Splits C] [HasPullbacks (Tot C)] {T U : Tot C} (i : T ⟶ U)

omit hZ [Splits C] [HasPullbacks (Tot C)] in
theorem comparison_naturality {X Y : C} (f : X ⟶ Y) :
    (PartialSlicePostcompose.functor i).map (AmbientSliceTuring.constantMap T.obj f) ≫
        PartialSliceTheoryComparison.baseComparison i Y =
      PartialSliceTheoryComparison.baseComparison i X ≫ AmbientSliceTuring.constantMap U.obj f := by
  apply Hom.ext
  change nearProd_map (𝟙 T.obj) f ≫ nearProd_map i.hom (𝟙 Y) =
    nearProd_map i.hom (𝟙 X) ≫ nearProd_map (𝟙 U.obj) f
  rw [PCategory.nearProd_comp, PCategory.nearProd_comp]
  simp only [Category.id_comp, Category.comp_id]

omit hZ in
theorem forward_naturality {X Y : C} (f : X ⟶ Y) :
    AmbientSliceTuring.constantMap T.obj f ≫ PartialSliceTheoryComparison.sentenceForward i Y =
      PartialSliceTheoryComparison.sentenceForward i X ≫
        (PartialSliceReindex.functor i).map (AmbientSliceTuring.constantMap U.obj f) := by
  calc
    _ = PartialSliceLeftAdjunction.lift i
        ((PartialSlicePostcompose.functor i).map (AmbientSliceTuring.constantMap T.obj f) ≫
          PartialSliceTheoryComparison.baseComparison i Y) :=
      (PartialSliceLeftAdjunction.lift_naturality_left i _ _).symm
    _ = PartialSliceLeftAdjunction.lift i
        (PartialSliceTheoryComparison.baseComparison i X ≫
          AmbientSliceTuring.constantMap U.obj f) :=
      congrArg (PartialSliceLeftAdjunction.lift i) (comparison_naturality i f)
    _ = _ := PartialSliceLeftAdjunction.lift_naturality_right i _ _

omit hZ in
def pullbackConstantIso (inverses : MonoInverses C) [Mono i] :
    ConstantFamilyProducts.constantFunctor T.obj ≅
      ConstantFamilyProducts.constantFunctor U.obj ⋙ PartialSliceReindex.functor i :=
  NatIso.ofComponents (PartialSliceTheoryComparison.sentenceIso i inverses)
    (forward_naturality i)

variable (point : Z ⟶ U)

omit [Splits C] [HasPullbacks (Tot C)] in
include hZ in
theorem point_mono : Mono point where
  right_cancellation _ _ _ := hZ.hom_ext _ _

def evaluation : Family U.obj ⥤ C :=
  PartialSliceReindex.functor point ⋙ AmbientPartialSlice.forget

def retraction (inverses : MonoInverses C) :
    ConstantFamilyProducts.constantFunctor U.obj ⋙ evaluation point ≅ 𝟭 C := by
  letI := point_mono hZ point
  exact Functor.isoWhiskerRight (pullbackConstantIso point inverses).symm
      AmbientPartialSlice.forget ≪≫
    constantTerminalIso hZ

omit hZ i in
theorem evaluation_restriction : PreservesRestriction (evaluation point) := by
  intro X Y f
  change ((PartialSliceReindex.functor point).map (rst f)).hom =
    CategoryTheory.RestrictionCategory.rst ((PartialSliceReindex.functor point).map f).hom
  rw [PartialSliceReindex.preserves_restriction]
  rfl

end CategoricalEssentialIncompleteness.V46.ConstantFamilyRetraction
