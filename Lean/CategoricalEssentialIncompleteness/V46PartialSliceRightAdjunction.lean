/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSliceLeftAdjunction

/-! # Pullback is left adjoint to postcomposition along a monomorphism -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialSliceRightAdjunction

open RestrictionSubobjects AmbientPartialSlice
variable {C : Type u} [Category.{v} C] [RestrictionCategory C] [Splits C]
variable [HasPullbacks (Tot C)] {T U : Tot C} (i : T ⟶ U)

def inclusionTotal (Y : Family U.obj) :
    (⟨(PartialSliceReindex.object i Y).base⟩ : Tot C) ⟶ ⟨Y.base⟩ :=
  pullback.fst (AmbientSliceProducts.totalProjection Y)
    (AmbientSliceProducts.totalProjection (PartialSliceReindex.baseFamily i))

variable [Mono i]

instance inclusionTotal_mono (Y : Family U.obj) : Mono (inclusionTotal i Y) := by
  change Mono (pullback.fst (AmbientSliceProducts.totalProjection Y) i)
  infer_instance

variable (inverses : MonoInverses C)

def inverseFirst (Y : Family U.obj) :
    Y ⟶ PartialSlicePostcompose.object i (PartialSliceReindex.object i Y) :=
  ⟨inverse inverses (inclusionTotal i Y), by
    have h := (PartialSliceReindex.first i Y).over
    rw [(AmbientPartialSlice.total_iff _).mp (PartialSliceReindex.first_total i Y),
      Category.id_comp] at h
    change (inclusionTotal i Y).hom ≫ Y.proj =
      (PartialSliceReindex.object i Y).proj ≫ i.hom at h
    change inverse inverses (inclusionTotal i Y) ≫
        ((PartialSliceReindex.object i Y).proj ≫ i.hom) =
      rst (inverse inverses (inclusionTotal i Y)) ≫ Y.proj
    rw [← h, ← Category.assoc]
    exact congrArg (fun k => k ≫ Y.proj) (inverse_hom inverses (inclusionTotal i Y))⟩

omit [Splits C] in
theorem first_inverseFirst (Y : Family U.obj) :
    PartialSliceReindex.first i Y ≫ inverseFirst i inverses Y =
      𝟙 (PartialSlicePostcompose.object i (PartialSliceReindex.object i Y)) :=
  Hom.ext (hom_inverse inverses (inclusionTotal i Y))

omit [Splits C] in
theorem inverseFirst_first (Y : Family U.obj) :
    inverseFirst i inverses Y ≫ PartialSliceReindex.first i Y = rst (inverseFirst i inverses Y) :=
  Hom.ext (inverse_hom inverses (inclusionTotal i Y))

/-- A partial morphism whose target factors through i already has its
domain inside the pullback of i. -/
theorem domain_absorb {X : Family T.obj} {Y : Family U.obj}
    (f : Y ⟶ PartialSlicePostcompose.object i X) :
    (inverseFirst i inverses Y ≫ PartialSliceReindex.first i Y) ≫ f = f := by
  let D := AmbientSliceProducts.restrictionProducts U.obj
  let h := D.pair (rst f) (f ≫ PartialSliceLeftAdjunction.toBase i X)
  have h0 : h ≫ D.fst Y (PartialSliceReindex.baseFamily i) = rst f := by
    change D.pair (rst f) (f ≫ PartialSliceLeftAdjunction.toBase i X) ≫ _ = rst f
    rw [D.pair_fst, rst_comp_of_isTotal f (PartialSliceLeftAdjunction.toBase_total i X)]
    exact (Idem.ofRestrict f).idem
  have h0' := congrArg (fun k : Y ⟶ Y => k.hom) h0
  change h.hom ≫ (PartialSliceReindex.first i Y).hom = rst f.hom at h0'
  have hp : (PartialSliceReindex.first i Y).hom ≫ (inverseFirst i inverses Y).hom =
      𝟙 (PartialSliceReindex.object i Y).base := hom_inverse inverses (inclusionTotal i Y)
  have he : (inverseFirst i inverses Y).hom ≫ (PartialSliceReindex.first i Y).hom =
      rst (inverseFirst i inverses Y).hom := inverse_hom inverses (inclusionTotal i Y)
  have hfix : rst f.hom ≫ rst (inverseFirst i inverses Y).hom = rst f.hom := by
    rw [← he, ← h0']
    change (h.hom ≫ (PartialSliceReindex.first i Y).hom) ≫
        ((inverseFirst i inverses Y).hom ≫ (PartialSliceReindex.first i Y).hom) =
      h.hom ≫ (PartialSliceReindex.first i Y).hom
    rw [Category.assoc, ← Category.assoc (PartialSliceReindex.first i Y).hom, hp]
    exact congrArg (fun k => h.hom ≫ k) (Category.id_comp (PartialSliceReindex.first i Y).hom)
  apply Hom.ext
  change ((inverseFirst i inverses Y).hom ≫ (PartialSliceReindex.first i Y).hom) ≫ f.hom = f.hom
  rw [he]
  calc
    _ = rst (inverseFirst i inverses Y).hom ≫ (rst f.hom ≫ f.hom) := by rw [rst_comp_self]
    _ = (rst f.hom ≫ rst (inverseFirst i inverses Y).hom) ≫ f.hom := by
      rw [← Category.assoc, rst_comm]
    _ = rst f.hom ≫ f.hom := by rw [hfix]
    _ = f.hom := rst_comp_self _

def restrict {X : Family T.obj} {Y : Family U.obj}
    (f : Y ⟶ PartialSlicePostcompose.object i X) : PartialSliceReindex.object i Y ⟶ X := by
  letI := PartialSlicePostcompose.full i inverses
  exact (PartialSlicePostcompose.functor i).preimage (X := PartialSliceReindex.object i Y) (Y := X)
    (PartialSliceReindex.first i Y ≫ f)

omit [Splits C] in
theorem restrict_value {X : Family T.obj} {Y : Family U.obj}
    (f : Y ⟶ PartialSlicePostcompose.object i X) :
    (PartialSlicePostcompose.functor i).map (restrict i inverses f) =
      PartialSliceReindex.first i Y ≫ f := by
  let := PartialSlicePostcompose.full i inverses
  exact (PartialSlicePostcompose.functor i).map_preimage _

def extend {X : Family T.obj} {Y : Family U.obj} (g : PartialSliceReindex.object i Y ⟶ X) :
    Y ⟶ PartialSlicePostcompose.object i X :=
  inverseFirst i inverses Y ≫ (PartialSlicePostcompose.functor i).map g

def homEquiv (Y : Family U.obj) (X : Family T.obj) :
    (PartialSliceReindex.object i Y ⟶ X) ≃ (Y ⟶ PartialSlicePostcompose.object i X) where
  toFun := extend i inverses
  invFun := restrict i inverses
  left_inv g := by
    apply (PartialSlicePostcompose.functor i).map_injective
    rw [restrict_value]
    change PartialSliceReindex.first i Y ≫
      (inverseFirst i inverses Y ≫ (PartialSlicePostcompose.functor i).map g) = _
    rw [← Category.assoc, first_inverseFirst, Category.id_comp]
  right_inv f := by
    change inverseFirst i inverses Y ≫
      (PartialSlicePostcompose.functor i).map (restrict i inverses f) = f
    rw [restrict_value, ← Category.assoc, domain_absorb]

theorem naturality_left {Y Y' : Family U.obj} {X : Family T.obj}
    (f : Y' ⟶ Y) (g : Y ⟶ PartialSlicePostcompose.object i X) :
    (homEquiv i inverses Y' X).symm (f ≫ g) =
      (PartialSliceReindex.functor i).map f ≫ (homEquiv i inverses Y X).symm g := by
  apply (PartialSlicePostcompose.functor i).map_injective
  change (PartialSlicePostcompose.functor i).map (restrict i inverses (f ≫ g)) =
    (PartialSlicePostcompose.functor i).map
      ((PartialSliceReindex.functor i).map f ≫ restrict i inverses g)
  rw [CategoryTheory.Functor.map_comp, restrict_value, restrict_value]
  apply Hom.ext
  change (PartialSliceReindex.first i Y').hom ≫ (f.hom ≫ g.hom) =
    (PartialSliceReindex.map i f).hom ≫ ((PartialSliceReindex.first i Y).hom ≫ g.hom)
  rw [← Category.assoc (PartialSliceReindex.map i f).hom,
    PartialSliceReindex.map_first, Category.assoc]

theorem naturality_right {Y : Family U.obj} {X X' : Family T.obj}
    (g : PartialSliceReindex.object i Y ⟶ X) (h : X ⟶ X') :
    (homEquiv i inverses Y X') (g ≫ h) =
      (homEquiv i inverses Y X) g ≫ (PartialSlicePostcompose.functor i).map h := by
  apply Hom.ext
  exact (Category.assoc (inverseFirst i inverses Y).hom g.hom h.hom).symm

def adjunction : PartialSliceReindex.functor i ⊣ PartialSlicePostcompose.functor i :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv i inverses
    homEquiv_naturality_left_symm := naturality_left i inverses
    homEquiv_naturality_right := naturality_right i inverses
  }

theorem unit_value (Y : Family U.obj) :
    (adjunction i inverses).unit.app Y = inverseFirst i inverses Y := by
  change inverseFirst i inverses Y ≫
    (PartialSlicePostcompose.functor i).map (𝟙 (PartialSliceReindex.object i Y)) = _
  rw [CategoryTheory.Functor.map_id]
  exact Category.comp_id (inverseFirst i inverses Y)

end CategoricalEssentialIncompleteness.V46.PartialSliceRightAdjunction
