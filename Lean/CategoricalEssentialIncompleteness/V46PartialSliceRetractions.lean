/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSliceTuring

/-! # Restriction terminal morphisms and total retractions in partial slices -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialSliceRetractions

open RestrictionSubobjects PartialSliceTuring

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [HasPullbacks (Tot C)]
variable (inverses : MonoInverses C) (T : Tot C)

def terminalObject : PartialMaps.Par (Over T) :=
  realizeObject T (AmbientPartialSlice.terminalFamily T.obj)

def terminate (X : PartialMaps.Par (Over T)) : X ⟶ terminalObject T :=
  (PartialSliceEquivalence.functor inverses T).preimage (X := X) (Y := terminalObject T)
    (AmbientPartialSlice.terminate ((PartialSliceEquivalence.functor inverses T).obj X))

theorem terminate_value (X : PartialMaps.Par (Over T)) :
    (PartialSliceEquivalence.functor inverses T).map (terminate inverses T X) =
      AmbientPartialSlice.terminate ((PartialSliceEquivalence.functor inverses T).obj X) :=
  (PartialSliceEquivalence.functor inverses T).map_preimage
    (X := X) (Y := terminalObject T) _

theorem terminate_total (X : PartialMaps.Par (Over T)) : isTotal (terminate inverses T X) := by
  apply (PartialSliceEquivalence.total_iff inverses T _).mp
  rw [terminate_value]
  exact AmbientPartialSlice.terminate_total _

theorem terminate_self : terminate inverses T (terminalObject T) = 𝟙 (terminalObject T) := by
  apply (PartialSliceEquivalence.functor inverses T).map_injective
  rw [terminate_value, CategoryTheory.Functor.map_id]
  exact AmbientPartialSlice.terminate_self

theorem terminate_naturality {X Y : PartialMaps.Par (Over T)} (f : X ⟶ Y) :
    f ≫ terminate inverses T Y = rst f ≫ terminate inverses T X := by
  apply (PartialSliceEquivalence.functor inverses T).map_injective
  rw [CategoryTheory.Functor.map_comp, terminate_value, CategoryTheory.Functor.map_comp,
    terminate_value, PartialSliceEquivalence.preserves_restrictions]
  exact AmbientPartialSlice.terminate_naturality _

theorem terminate_unique {X : PartialMaps.Par (Over T)} (f : X ⟶ terminalObject T)
    (hf : isTotal f) : f = terminate inverses T X := by
  apply (PartialSliceEquivalence.functor inverses T).map_injective
  rw [terminate_value]
  exact AmbientPartialSlice.terminate_unique _
    ((PartialSliceEquivalence.total_iff inverses T f).mpr hf)

/-- Every total base embedding into Q induces a total embedding of the partial-slice
object into the constant family T×Q, with a partial retraction over T. -/
theorem total_retract {Q : C} (X : PartialMaps.Par (Over T))
    (m : ((PartialSliceEquivalence.functor inverses T).obj X).base ⟶ Q)
    (hm : isTotal m) (r : Q ⟶ ((PartialSliceEquivalence.functor inverses T).obj X).base)
    (hmr : m ≫ r = 𝟙 _) :
    ∃ (j : X ⟶ constantObject T Q) (s : constantObject T Q ⟶ X),
      isTotal j ∧ j ≫ s = 𝟙 X ∧ s ≫ j = rst s := by
  let F := PartialSliceEquivalence.functor inverses T
  obtain ⟨j, s, hj, hj0, hjs, hsj, hs0⟩ := SliceTuringParameters.total_retract_over
    inverses (F.obj X).proj (F.obj X).total m hm r hmr
  let j' : F.obj X ⟶ F.obj (constantObject T Q) := ⟨j, by
    change j ≫ p0 T.obj Q = CategoryTheory.RestrictionCategory.rst j ≫ (F.obj X).proj
    rw [hj0, hj, Category.id_comp]⟩
  let s' : F.obj (constantObject T Q) ⟶ F.obj X := ⟨s, hs0⟩
  let a : X ⟶ constantObject T Q := F.preimage (X := X) (Y := constantObject T Q) j'
  let b : constantObject T Q ⟶ X := F.preimage (X := constantObject T Q) (Y := X) s'
  have ha : F.map a = j' := F.map_preimage (X := X) (Y := constantObject T Q) j'
  have hb : F.map b = s' := F.map_preimage (X := constantObject T Q) (Y := X) s'
  refine ⟨a, b, ?_, ?_, ?_⟩
  · apply (PartialSliceEquivalence.total_iff inverses T a).mp
    change isTotal (F.map a)
    rw [ha]
    exact (AmbientPartialSlice.total_iff j').mpr hj
  · apply F.map_injective
    rw [F.map_comp, ha, hb, F.map_id]
    exact AmbientPartialSlice.Hom.ext hjs
  · apply F.map_injective
    rw [F.map_comp, ha, hb, PartialSliceEquivalence.preserves_restrictions, hb]
    exact AmbientPartialSlice.Hom.ext hsj

include inverses in
theorem exists_total_retract {Q : C}
    (hQ : ∀ Y : C, ∃ (m : Y ⟶ Q) (r : Q ⟶ Y), isTotal m ∧ m ≫ r = 𝟙 Y)
    (X : PartialMaps.Par (Over T)) :
    ∃ (j : X ⟶ constantObject T Q) (s : constantObject T Q ⟶ X),
      isTotal j ∧ j ≫ s = 𝟙 X ∧ s ≫ j = rst s := by
  obtain ⟨m, r, hm, hmr⟩ := hQ ((PartialSliceEquivalence.functor inverses T).obj X).base
  exact total_retract inverses T X m hm r hmr

end CategoricalEssentialIncompleteness.V46.PartialSliceRetractions
