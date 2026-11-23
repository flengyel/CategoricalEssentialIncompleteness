/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSliceSpanChangeBase
public import CategoricalEssentialIncompleteness.V46PartialMapTotals

/-! # Totality of the slice unit at an arbitrary family -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialSliceChangeBase

open RestrictionSubobjects
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [HasPullbacks (Tot C)] {T U : Tot C} (i : T ⟶ U) [Mono i] (inverses : MonoInverses C)

/-- At a family over `U`, the unit is total exactly when that family factors through `i`. -/
theorem right_unit_total_iff (Y : PartialMaps.Par (Over U)) :
    isTotal ((rightAdjunction i inverses).unit.app Y) ↔
      ∃ r : Y.obj.left ⟶ T, r ≫ i = Y.obj.hom := by
  rw [right_unit_span]
  let m := pullbackInclusion i inverses Y
  let s := PartialMaps.Raw.monoInverse m
  change isTotal (PartialMaps.ofSpan s) ↔ _
  constructor
  · intro h
    let : IsIso m := PartialMaps.Raw.left_isIso_of_total s h
    let : IsIso (pullback.fst Y.obj.hom i) := (Over.forget U).map_isIso m
    refine ⟨inv (pullback.fst Y.obj.hom i) ≫ pullback.snd Y.obj.hom i, ?_⟩
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  · rintro ⟨r, h⟩
    let e := PartialMaps.pullbackFactorIso Y.obj.hom i r h
    let E : ((postcompose i).obj ((reindex i inverses).obj Y)).obj ≅ Y.obj :=
      Over.isoMk e (pullback.condition (f := Y.obj.hom) (g := i))
    let : IsIso m := E.isIso_hom
    let : IsIso s.l := ‹IsIso m›
    rw [PartialMaps.ofSpan_eq_of_iso (PartialMaps.Raw.totalIso s)]
    exact PartialMaps.ofTotal_total _

end CategoricalEssentialIncompleteness.V46.PartialSliceChangeBase
