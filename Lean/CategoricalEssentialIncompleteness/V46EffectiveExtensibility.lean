/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakNativeDecision

/-! # A complete consistent presentation and effective extensibility

At the empty family of additional axioms, a complete presentation has no
independent sentence. The complete theory used here has decidable axiom codes.
This gives the boundary of the definition at the opening of §8.3.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.Entailment
open Janiczak Janiczak.NativeInput

namespace CategoricalEssentialIncompleteness.V46.EffectiveExtensibility

/-- The complete theory determined by the empty set of finite class sizes is
consistent, has recursive axiom codes, and admits no independent-sentence
assignment for any family of additional axioms with an empty fiber. -/
theorem exists_complete_presentation_without_extender :
    ∃ T : Theory FOL.L, Entailment.Consistent T ∧
      ComputablePred (fun w : ℕ => ∃ p : Sentence FOL.L, Encodable.encode p = w ∧ p ∈ T) ∧
      ∀ (additional : ℕ → Set (Sentence FOL.L)), (∃ i, additional i = ∅) →
        ¬ ∃ q : ℕ → Sentence FOL.L, ∀ i, Entailment.Consistent (T ∪ additional i) →
          (¬ (T ∪ additional i) ⊢ q i) ∧ (¬ (T ∪ additional i) ⊢ ∼(q i)) := by
  classical
  let T := completeTheory (∅ : Set ℕ)
  let M := canonical (∅ : Set ℕ)
  let _ := M.inhabited
  let _ := FOL.model M
  have hc : Entailment.Consistent T := completeTheory_consistent ∅
  have hm : M.Carrier↓[FOL.L] ⊧* T := ⟨fun _ h => h⟩
  have mem_iff (p : Sentence FOL.L) : p ∈ T ↔ T ⊢ p := by
    refine ⟨Entailment.by_axm, fun h => ?_⟩
    exact consequence_iff.mp (Theory.Proof.sound h) M.Carrier hm
  have he : ComputablePred (fun n : ℕ => n ∈ (∅ : Set ℕ)) := by
    refine ComputablePred.computable_iff.mpr ⟨fun _ : ℕ => false, Computable.const false, ?_⟩
    funext n
    simp
  have axiom_words :
      (fun w : ℕ => ∃ p : Sentence FOL.L, Encodable.encode p = w ∧ p ∈ T) =
      (fun w : ℕ => ∃ p : Sentence FOL.L, Encodable.encode p = w ∧ T ⊢ p) := by
    funext w
    simp only [mem_iff]
  refine ⟨T, hc, axiom_words ▸ ?_, ?_⟩
  · exact computable_completeTheory_words he
  · rintro additional ⟨i, hi⟩ ⟨q, all_indices⟩
    have equal_base : T ∪ additional i = T := by rw [hi, Set.union_empty]
    obtain ⟨hp, hn⟩ := (equal_base ▸ all_indices i) hc
    by_cases h : Semiformula.Realize M.Carrier (q i)
    · exact hp ((mem_iff _).mp h)
    · apply hn
      apply (mem_iff _).mp
      change Semiformula.Realize M.Carrier (∼ (q i))
      simpa using h

end CategoricalEssentialIncompleteness.V46.EffectiveExtensibility
