import CategoricalEssentialIncompleteness.V46JaniczakNativeDecision

open FFL FFL.FirstOrder FFL.Entailment
open Janiczak Janiczak.NativeInput

namespace FirstReaderCompletePresentation

/-- A concrete computably axiomatizable, consistent theory defeats every proposed
independent-sentence assignment at any index enumerating the empty additional axioms. -/
theorem exists_complete_presentation :
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

#print axioms exists_complete_presentation

end FirstReaderCompletePresentation
