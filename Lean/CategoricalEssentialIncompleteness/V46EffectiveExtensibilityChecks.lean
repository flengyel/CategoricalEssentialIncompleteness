/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46EffectiveExtensibility

/-! # The empty extension of a complete presentation -/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder

namespace CategoricalEssentialIncompleteness.V46.EffectiveExtensibility.Checks

theorem consistent_without_independent_sentence :
    ∃ T : Theory Janiczak.FOL.L, Entailment.Consistent T ∧
      ComputablePred (fun n : ℕ ↦ ∃ p : Sentence Janiczak.FOL.L, Encodable.encode p = n ∧ p ∈ T) ∧
      ¬ ∃ p : Sentence Janiczak.FOL.L, (¬ T ⊢ p) ∧ (¬ T ⊢ ∼p) := by
  obtain ⟨T, consistent, computableCodes, noSelector⟩ :=
    exists_complete_presentation_without_extender
  refine ⟨T, consistent, computableCodes, ?_⟩
  rintro ⟨p, hp⟩
  apply noSelector (fun _ ↦ ∅) ⟨0, rfl⟩
  exact ⟨fun _ ↦ p, fun _ _ ↦ by simpa only [Set.union_empty] using hp⟩

end CategoricalEssentialIncompleteness.V46.EffectiveExtensibility.Checks

open CategoricalEssentialIncompleteness.V46.EffectiveExtensibility

#print axioms exists_complete_presentation_without_extender
#print axioms Checks.consistent_without_independent_sentence
