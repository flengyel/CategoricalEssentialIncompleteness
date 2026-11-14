/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSliceReindex
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Postcomposition is left adjoint to pullback on partial slices -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialSliceLeftAdjunction

open RestrictionSubobjects AmbientPartialSlice
variable {C : Type u} [Category.{v} C] [RestrictionCategory C] [Splits C]
variable [HasPullbacks (Tot C)] {T U : Tot C} (i : T ⟶ U)

def toBase (X : Family T.obj) :
    PartialSlicePostcompose.object i X ⟶ PartialSliceReindex.baseFamily i :=
  ⟨X.proj, by
    change X.proj ≫ i.hom = rst X.proj ≫ (X.proj ≫ i.hom)
    rw [X.total, Category.id_comp]⟩

omit [Splits C] [HasPullbacks (Tot C)] in
theorem toBase_total (X : Family T.obj) : isTotal (toBase i X) :=
  (AmbientPartialSlice.total_iff _).mpr X.total

def lift {X : Family T.obj} {Y : Family U.obj}
    (f : PartialSlicePostcompose.object i X ⟶ Y) : X ⟶ PartialSliceReindex.object i Y :=
  ⟨(AmbientSliceProducts.pair f (toBase i X)).hom, by
    have h := congrArg
      (fun k : PartialSlicePostcompose.object i X ⟶ PartialSliceReindex.baseFamily i => k.hom)
      (AmbientSliceProducts.pair_snd f (toBase i X))
    have hr := congrArg
      (fun k : PartialSlicePostcompose.object i X ⟶ PartialSlicePostcompose.object i X => k.hom)
      (AmbientSliceProducts.pair_restriction f (toBase i X))
    rw [toBase_total, Category.comp_id] at hr
    change rst (AmbientSliceProducts.pair f (toBase i X)).hom = rst f.hom at hr
    change (AmbientSliceProducts.pair f (toBase i X)).hom ≫
      (AmbientSliceProducts.second Y (PartialSliceReindex.baseFamily i)).hom =
        rst f.hom ≫ X.proj at h
    change _ ≫ (PartialSliceReindex.object i Y).proj =
      rst (AmbientSliceProducts.pair f (toBase i X)).hom ≫ X.proj
    rw [hr]
    exact h⟩

theorem lift_first {X : Family T.obj} {Y : Family U.obj}
    (f : PartialSlicePostcompose.object i X ⟶ Y) :
    (lift i f).hom ≫ (PartialSliceReindex.first i Y).hom = f.hom := by
  have h := congrArg (fun k : PartialSlicePostcompose.object i X ⟶ Y => k.hom)
    (AmbientSliceProducts.pair_fst f (toBase i X))
  rw [toBase_total, Category.id_comp] at h
  exact h

def descend {X : Family T.obj} {Y : Family U.obj} (g : X ⟶ PartialSliceReindex.object i Y) :
    PartialSlicePostcompose.object i X ⟶ Y :=
  (PartialSlicePostcompose.functor i).map g ≫ PartialSliceReindex.first i Y

def homEquiv (X : Family T.obj) (Y : Family U.obj) :
    (PartialSlicePostcompose.object i X ⟶ Y) ≃ (X ⟶ PartialSliceReindex.object i Y) where
  toFun := lift i
  invFun := descend i
  left_inv f := Hom.ext (lift_first i f)
  right_inv g := by
    apply PartialSliceReindex.hom_ext i
    exact lift_first i (descend i g)

theorem naturality_left {X X' : Family T.obj} {Y : Family U.obj}
    (f : X' ⟶ X) (g : X ⟶ PartialSliceReindex.object i Y) :
    (homEquiv i X' Y).symm (f ≫ g) =
      (PartialSlicePostcompose.functor i).map f ≫ (homEquiv i X Y).symm g := by
  apply Hom.ext
  exact Category.assoc f.hom g.hom (PartialSliceReindex.first i Y).hom

theorem naturality_right {X : Family T.obj} {Y Y' : Family U.obj}
    (f : PartialSlicePostcompose.object i X ⟶ Y) (g : Y ⟶ Y') :
    (homEquiv i X Y') (f ≫ g) = (homEquiv i X Y) f ≫ (PartialSliceReindex.functor i).map g := by
  apply PartialSliceReindex.hom_ext i
  change (lift i (f ≫ g)).hom ≫ (PartialSliceReindex.first i Y').hom =
    ((lift i f).hom ≫ (PartialSliceReindex.map i g).hom) ≫ (PartialSliceReindex.first i Y').hom
  rw [lift_first, Category.assoc, PartialSliceReindex.map_first,
    ← Category.assoc, lift_first]
  rfl

theorem lift_naturality_left {X X' : Family T.obj} {Y : Family U.obj}
    (f : X' ⟶ X) (g : PartialSlicePostcompose.object i X ⟶ Y) :
    lift i ((PartialSlicePostcompose.functor i).map f ≫ g) = f ≫ lift i g := by
  apply PartialSliceReindex.hom_ext i
  change (lift i ((PartialSlicePostcompose.functor i).map f ≫ g)).hom ≫
      (PartialSliceReindex.first i Y).hom =
    (f.hom ≫ (lift i g).hom) ≫ (PartialSliceReindex.first i Y).hom
  rw [lift_first, Category.assoc, lift_first]
  rfl

theorem lift_naturality_right {X : Family T.obj} {Y Y' : Family U.obj}
    (f : PartialSlicePostcompose.object i X ⟶ Y) (g : Y ⟶ Y') :
    lift i (f ≫ g) = lift i f ≫ (PartialSliceReindex.functor i).map g :=
  naturality_right i f g

theorem lift_total {X : Family T.obj} {Y : Family U.obj}
    (f : PartialSlicePostcompose.object i X ⟶ Y) (hf : isTotal f) : isTotal (lift i f) := by
  apply (AmbientPartialSlice.total_iff _).mpr
  have h := congrArg
    (fun k : PartialSlicePostcompose.object i X ⟶ PartialSlicePostcompose.object i X => k.hom)
    (AmbientSliceProducts.pair_restriction f (toBase i X))
  rw [hf, toBase_total, Category.id_comp] at h
  exact h

def adjunction : PartialSlicePostcompose.functor i ⊣ PartialSliceReindex.functor i :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv i
    homEquiv_naturality_left_symm := naturality_left i
    homEquiv_naturality_right := naturality_right i
  }

theorem counit_value (Y : Family U.obj) :
    (adjunction i).counit.app Y = PartialSliceReindex.first i Y := by
  change (PartialSlicePostcompose.functor i).map (𝟙 (PartialSliceReindex.object i Y)) ≫ _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end CategoricalEssentialIncompleteness.V46.PartialSliceLeftAdjunction
