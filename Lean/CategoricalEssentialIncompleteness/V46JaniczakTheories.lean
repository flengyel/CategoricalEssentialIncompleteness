/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakLanguage

/-!
# Models and consequence for the equivalence-relation language

An axiom with free variables denotes its universal closure. The full theory of a nonempty structure has that structure as a model.
-/

@[expose] public section

set_option autoImplicit false

namespace Janiczak

structure Structure where
  Carrier : Type
  inhabited : Nonempty Carrier
  rel : Carrier → Carrier → Prop

namespace Structure

def Valid (M : Structure) (p : Formula) := ∀ v : ℕ → M.Carrier, p.Holds M.rel v

def Models (M : Structure) (T : Set Formula) := ∀ p ∈ T, M.Valid p

theorem hasValuation (M : Structure) : Nonempty (ℕ → M.Carrier) :=
  M.inhabited.map fun x _ ↦ x

end Structure

/-- A theory is consistent if its axioms have a nonempty model. -/
def Consistent (T : Set Formula) : Prop := ∃ M : Structure, M.Models T

/-- A formula is a consequence of the axioms if its universal closure holds in every model. -/
def Consequence (T : Set Formula) (p : Formula) := ∀ M : Structure, M.Models T → M.Valid p

theorem Consequence.of_mem {T : Set Formula} {p : Formula} (h : p ∈ T) : Consequence T p :=
  fun _ hT ↦ hT _ h

theorem Consequence.compatible {T : Set Formula} {p : Formula} (hT : Consistent T) :
    Consequence T p → ¬ Consequence T p.neg := by
  obtain ⟨M, hM⟩ := hT
  obtain ⟨v⟩ := M.hasValuation
  exact fun hp hn ↦ hn M hM v (hp M hM v)

/-- The full theory of a structure decides consequence by its own satisfaction predicate. -/
theorem consequence_fullTheory (M : Structure) (p : Formula) :
    Consequence (Set.ofPred M.Valid) p ↔ M.Valid p :=
  ⟨fun h ↦ h M (fun _ hq ↦ hq), fun h ↦ Consequence.of_mem h⟩

end Janiczak
