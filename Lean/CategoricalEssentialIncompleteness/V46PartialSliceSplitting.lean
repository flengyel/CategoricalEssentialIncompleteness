/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSliceTuring

/-! # Splitting restriction idempotents in actual partial slices -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialSliceSplitting

open RestrictionSubobjects

variable {C : Type u} [Category.{v} C] [RestrictionCategory C] [Splits C]

theorem ambient_splitting {T : C} {X : AmbientPartialSlice.Family T} (a : Idem X) :
    ∃ (Z : AmbientPartialSlice.Family T) (m : Z ⟶ X) (r : X ⟶ Z),
      isTotal m ∧ m ≫ r = 𝟙 Z ∧ r ≫ m = a.hom := by
  let e : Idem X.base := ⟨a.hom.hom, congrArg AmbientPartialSlice.Hom.hom a.restriction⟩
  obtain ⟨Z, m, r, hm, hmr, hrm⟩ := Splits.splitting e
  have hr : rst r = a.hom.hom := by
    rw [← rst_comp_of_isTotal r hm, hrm, e.restriction]
  let Z' : AmbientPartialSlice.Family T :=
    ⟨Z, m ≫ X.proj, isTotal_comp hm X.total⟩
  let m' : Z' ⟶ X := ⟨m, by
    change m ≫ X.proj = rst m ≫ (m ≫ X.proj)
    rw [hm, Category.id_comp]⟩
  let r' : X ⟶ Z' := ⟨r, by
    change r ≫ (m ≫ X.proj) = rst r ≫ X.proj
    rw [← Category.assoc, hrm, hr]⟩
  refine ⟨Z', m', r', (AmbientPartialSlice.total_iff m').mpr hm,
    AmbientPartialSlice.Hom.ext hmr, AmbientPartialSlice.Hom.ext hrm⟩

theorem ambientSplits (T : C) : Splits (AmbientPartialSlice.Family T) where
  splitting := ambient_splitting

variable [HasPullbacks (Tot C)]
variable (inverses : MonoInverses C) (T : Tot C)

include inverses in
/-- The literal family model allows the splitting object and both morphisms
to be lifted back into the actual monic-span quotient. -/
theorem splitting {X : PartialMaps.Par (Over T)} (a : Idem X) :
    ∃ (Z : PartialMaps.Par (Over T)) (m : Z ⟶ X) (r : X ⟶ Z),
      isTotal m ∧ m ≫ r = 𝟙 Z ∧ r ≫ m = a.hom := by
  let F := PartialSliceEquivalence.functor inverses T
  let e : Idem (F.obj X) := ⟨F.map a.hom, by
    rw [← PartialSliceEquivalence.preserves_restrictions, a.restriction]⟩
  obtain ⟨Z, m, r, hm, hmr, hrm⟩ := ambient_splitting e
  let Z' : PartialMaps.Par (Over T) := ⟨Over.mk (⟨Z.proj, Z.total⟩ : (⟨Z.base⟩ : Tot C) ⟶ T)⟩
  let m' : Z' ⟶ X := F.preimage (X := Z') (Y := X) m
  let r' : X ⟶ Z' := F.preimage (X := X) (Y := Z') r
  have hmv : F.map m' = m := F.map_preimage (X := Z') (Y := X) m
  have hrv : F.map r' = r := F.map_preimage (X := X) (Y := Z') r
  refine ⟨Z', m', r', ?_, ?_, ?_⟩
  · apply (PartialSliceEquivalence.total_iff inverses T m').mp
    change isTotal (F.map m')
    rw [hmv]
    exact hm
  · apply F.map_injective
    rw [F.map_comp, hmv, hrv, F.map_id]
    exact hmr
  · apply F.map_injective
    rw [F.map_comp, hmv, hrv]
    exact hrm

include inverses in
theorem partialSliceSplits : Splits (PartialMaps.Par (Over T)) where
  splitting := splitting inverses T

end CategoricalEssentialIncompleteness.V46.PartialSliceSplitting
