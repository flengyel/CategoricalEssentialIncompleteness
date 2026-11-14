/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46Inference
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Total subobjects under a functor preserving finite limits -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.FiniteLimitSubobjects

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [Regular D] (G : C ⥤ D) [PreservesFiniteLimits G]

local instance preservesMonos : G.PreservesMonomorphisms := by infer_instance

def object {S : C} (A : Subobject S) : Subobject (G.obj S) := Subobject.mk (G.map A.arrow)

omit [Regular C] [Regular D] in
theorem object_monotone {S : C} : Monotone (object G (S := S)) := by
  intro A B h
  apply Subobject.mk_le_mk_of_comm (G.map (Subobject.ofLE A B h))
  rw [← G.map_comp, Subobject.ofLE_arrow]

omit [Regular C] [Regular D] in
theorem object_mk {M S : C} (m : M ⟶ S) [Mono m] :
    object G (Subobject.mk m) = Subobject.mk (G.map m) := by
  apply Subobject.mk_eq_mk_of_comm _ _ (G.mapIso (Subobject.underlyingIso m))
  change G.map (Subobject.underlyingIso m).hom ≫ G.map m = G.map (Subobject.mk m).arrow
  rw [← G.map_comp, Subobject.underlyingIso_hom_comp_eq_mk]

theorem object_pullback {S T : C} (f : S ⟶ T) (A : Subobject T) :
    object G ((Subobject.pullback f).obj A) =
      (Subobject.pullback (G.map f)).obj (object G A) := by
  rw [Subobject.pullback_obj f A, object_mk]
  exact (Subobject.pullback_obj_mk ((IsPullback.of_hasPullback A.arrow f).map G)).symm

end CategoricalEssentialIncompleteness.V46.FiniteLimitSubobjects
