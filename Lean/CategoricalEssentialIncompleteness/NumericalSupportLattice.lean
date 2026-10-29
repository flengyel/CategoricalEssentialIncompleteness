/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.NumericalUnions
import CategoricalEssentialIncompleteness.PERExtensive
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Lattice operations on support subobjects

Full and empty supports represent the top and bottom subobjects of an equality
PER. Intersections represent meets. For two c.e. supports, their union represents
the categorical join by the dovetailing construction in `NumericalUnions`.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace NumericalPER

@[simp] theorem supportSubobject_top (X : Set ℕ) :
    supportSubobject X (Set.Subset.refl X) = ⊤ := by
  have h : inclusion (Set.Subset.refl X) = 𝟙 (discrete X) := by
    apply Quotient.sound
    exact Representative.equiv_of_val_eq _ _ rfl
  simpa only [supportSubobject, h] using (Subobject.top_eq_id (discrete X)).symm

def discreteEmptyIsInitial : IsInitial (discrete (∅ : Set ℕ)) :=
  IsInitial.ofUniqueHom (fun R ↦ ofRepresentative
    { val := fun _ ↦ Part.none
      computable := Partrec.none
      total := fun _ h ↦ False.elim h.1
      respects := fun h ↦ False.elim h.1 }) (by
    intro R f
    induction f using Quotient.inductionOn with | _ f =>
      apply Quotient.sound
      exact fun _ h ↦ False.elim h.1)

@[simp] theorem supportSubobject_bot (X : Set ℕ) :
    supportSubobject ∅ (Set.empty_subset X) = ⊥ := by
  rw [Subobject.bot_eq_initial_to]
  exact Subobject.mk_eq_mk_of_comm _ _
    (discreteEmptyIsInitial.uniqueUpToIso initialIsInitial)
    (discreteEmptyIsInitial.hom_ext _ _)

@[simp] theorem supportSubobject_inf {A B X : Set ℕ}
    (hA : A ⊆ X) (hB : B ⊆ X) :
    supportSubobject (A ∩ B) (Set.inter_subset_left.trans hA) =
      supportSubobject A hA ⊓ supportSubobject B hB := by
  symm
  have hi := Subobject.inf_eq_map_pullback' (MonoOver.mk (inclusion hA))
    (supportSubobject B hB)
  change supportSubobject A hA ⊓ supportSubobject B hB =
    (Subobject.map (inclusion hA)).obj
      ((Subobject.pullback (inclusion hA)).obj (supportSubobject B hB)) at hi
  rw [hi]
  have hp := Subobject.pullback_obj_mk (inverse_isPullback (inclusionRepresentative hA) hB).flip
  change (Subobject.pullback (inclusion hA)).obj (supportSubobject B hB) = _ at hp
  rw [hp, Subobject.map_mk]
  simp only [inclusion_comp]
  apply (supportSubobject_eq_iff _ _).mpr
  ext n
  simp [inverseSupport, inclusionRepresentative]

@[simp] theorem supportSubobject_sup {A B X : Set ℕ}
    (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B)) (hAX : A ⊆ X) (hBX : B ⊆ X) :
    supportSubobject (A ∪ B) (Set.union_subset hAX hBX) =
      supportSubobject A hAX ⊔ supportSubobject B hBX :=
  (enumerable_union_isLUB hA hB hAX hBX).unique isLUB_pair

end NumericalPER
end CategoricalEssentialIncompleteness
