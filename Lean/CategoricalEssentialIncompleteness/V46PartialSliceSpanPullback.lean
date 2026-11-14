/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSliceSpanChangeBase
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Reindexing agrees with ordinary pullback of monic spans -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialMaps

variable {D : Type u} [Category.{v} D] [HasPullbacks D]

theorem ofSpan_factorization {X Y : Par D} (s : Raw X Y) :
    ofSpan s = inverseMono (X := ⟨s.apex⟩) (Y := X) s.l ≫
      ofTotal (X := ⟨s.apex⟩) (Y := Y) s.r := by
  symm
  apply ofSpan_eq_of_iso
  refine CategoryTheory.Span.mkIso
    (asIso (pullback.fst (𝟙 s.apex) (𝟙 s.apex))) ?_ ?_
  · rfl
  · change pullback.fst (𝟙 s.apex) (𝟙 s.apex) ≫ s.r =
      pullback.snd (𝟙 s.apex) (𝟙 s.apex) ≫ s.r
    have h := pullback.condition (f := 𝟙 s.apex) (g := 𝟙 s.apex)
    simpa only [Category.comp_id] using congrArg (fun k => k ≫ s.r) h

end CategoricalEssentialIncompleteness.V46.PartialMaps

namespace CategoricalEssentialIncompleteness.V46.PartialSliceChangeBase

open RestrictionSubobjects
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [HasPullbacks (Tot C)] {T U : Tot C} (i : T ⟶ U) (inverses : MonoInverses C)

local instance pullbackMonos : (Over.pullback i).PreservesMonomorphisms := by infer_instance
local instance pullbackPullbacks : PreservesLimitsOfShape WalkingCospan (Over.pullback i) :=
  inferInstance

def spanPullback : PartialMaps.Par (Over U) ⥤ PartialMaps.Par (Over T) :=
  PartialMaps.inducedFunctor (Over.pullback i)

omit i in
theorem value_ofTotal (P : Tot C) {X Y : PartialMaps.Par (Over P)} (f : X.obj ⟶ Y.obj) :
    ((PartialSliceEquivalence.functor inverses P).map (PartialMaps.ofTotal f)).hom =
      f.left.hom := by
  change inverse inverses (𝟙 X.obj.left) ≫ f.left.hom = f.left.hom
  have h := hom_inverse inverses (𝟙 X.obj.left)
  change (𝟙 X.obj.left.obj) ≫ inverse inverses (𝟙 X.obj.left) = 𝟙 X.obj.left.obj at h
  rw [Category.id_comp] at h
  rw [h, Category.id_comp]

theorem reindex_ofTotal {X Y : PartialMaps.Par (Over U)} (f : X.obj ⟶ Y.obj) :
    (reindex i inverses).map (PartialMaps.ofTotal f) =
      PartialMaps.ofTotal ((Over.pullback i).map f) := by
  apply (PartialSliceEquivalence.functor inverses T).map_injective
  rw [reindex_value]
  apply PartialSliceReindex.hom_ext i
    (X := PartialSliceReindex.object i ((PartialSliceEquivalence.functor inverses U).obj X))
    (Y := (PartialSliceEquivalence.functor inverses U).obj Y)
  change (PartialSliceReindex.map i
      ((PartialSliceEquivalence.functor inverses U).map (PartialMaps.ofTotal f))).hom ≫
        (PartialSliceReindex.first i ((PartialSliceEquivalence.functor inverses U).obj Y)).hom =
    ((PartialSliceEquivalence.functor inverses T).map
      (PartialMaps.ofTotal ((Over.pullback i).map f))).hom ≫
        (PartialSliceReindex.first i ((PartialSliceEquivalence.functor inverses U).obj Y)).hom
  rw [PartialSliceReindex.map_first, value_ofTotal, value_ofTotal]
  have h : ((Over.pullback i).map f).left ≫ pullback.fst Y.obj.hom i =
      pullback.fst X.obj.hom i ≫ f.left := by
    dsimp only [Over.pullback]
    exact pullback.lift_fst _ _ _
  exact (congrArg (fun k : pullback X.obj.hom i ⟶ Y.obj.left => k.hom) h).symm

theorem reindex_inverseMono {X Y : PartialMaps.Par (Over U)} (m : X.obj ⟶ Y.obj) [Mono m] :
    (reindex i inverses).map (PartialMaps.inverseMono m) =
      PartialMaps.inverseMono ((Over.pullback i).map m) := by
  apply MonicSpanValues.partial_inverse_unique (PartialMaps.ofTotal ((Over.pullback i).map m))
  · rw [← reindex_ofTotal i inverses m, ← CategoryTheory.Functor.map_comp,
      PartialMaps.total_inverseMono, CategoryTheory.Functor.map_id]
    rfl
  · rw [← reindex_ofTotal i inverses m, ← CategoryTheory.Functor.map_comp,
      PartialMaps.inverseMono_total, reindex_restriction]
  · exact PartialMaps.total_inverseMono _
  · exact PartialMaps.inverseMono_total _

/-- This equality identifies the constructed reindexing with the functor
that pulls back each apex and both legs of every monic span. -/
theorem reindex_eq_spanPullback : reindex i inverses = spanPullback i := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  induction f using Quotient.inductionOn with | _ s =>
    change (reindex i inverses).map (PartialMaps.ofSpan s) =
      (spanPullback i).map (PartialMaps.ofSpan s)
    rw [PartialMaps.ofSpan_factorization s, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, reindex_inverseMono i inverses, reindex_ofTotal i inverses]
    change _ = (PartialMaps.inducedFunctor (Over.pullback i)).map _ ≫
      (PartialMaps.inducedFunctor (Over.pullback i)).map _
    rw [PartialMaps.inducedFunctor_inverseMono, PartialMaps.inducedFunctor_ofTotal]

end CategoricalEssentialIncompleteness.V46.PartialSliceChangeBase
