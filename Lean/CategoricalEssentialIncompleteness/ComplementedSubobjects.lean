/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.CharacteristicArrows
public import CategoricalEssentialIncompleteness.SubobjectPredicates

/-!
# Complemented subobjects and morphisms to two truth values

In a regular finitely extensive category, a subobject is complemented exactly when it
is the upper fiber of a morphism to `1 + 1`.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness

variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]

namespace Two

/-- The lower and upper truth-value inclusions are complementary subobjects. -/
theorem points_isCompl :
    IsCompl (Subobject.mk (point (C := C) false)) (Subobject.mk (point (C := C) true)) := by
  have h : coprod.desc (point (C := C) false) (point (C := C) true) = 𝟙 (Two C) := by
    simp [point]
  apply IsCompl.of_eq
  · apply (PresentationLemmas.mono_copair_iff _ _).mp
    rw [h]
    infer_instance
  · have ht : imageSubobject (coprod.desc (point (C := C) false) (point (C := C) true)) = ⊤ :=
      (PresentationLemmas.image_eq_top_iff_regularEpi _).mpr (by rw [h]; infer_instance)
    simpa only [PresentationLemmas.image_copair, imageSubobject_mono] using ht

/-- The two fibers of any morphism to two truth values are complementary. -/
theorem boundFibers_isCompl {X : C} (f : X ⟶ Two C) :
    IsCompl (boundFiber f (point false)) (boundFiber f (point true)) := by
  rw [PresentationLemmas.boundFiber_eq_pullback, PresentationLemmas.boundFiber_eq_pullback]
  exact (ComplementaryPair.map (SubobjectPredicates.pullbackHom f)
    ⟨_, _, points_isCompl⟩).compl

end Two

/-- A complemented subobject is exactly an upper truth-value fiber. -/
theorem isComplemented_iff_exists_characteristic {X : C} (a : Subobject X) :
    IsComplemented a ↔ ∃ f : X ⟶ Two C, boundFiber f (Two.point true) = a := by
  constructor
  · rintro ⟨b, hb⟩
    let p : SubobjectPartition X := ⟨a, b, hb⟩
    exact ⟨p.characteristic, p.characteristic_positive⟩
  · rintro ⟨f, rfl⟩
    exact ⟨boundFiber f (Two.point false), (Two.boundFibers_isCompl f).symm⟩

end CategoricalEssentialIncompleteness
