import CategoricalEssentialIncompleteness.V46SyntacticDerivationRecords

/-! Exact finite-record constructor equations for partial arithmetic transitions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.Records
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (g : Transition)

/-- The first transition and the remaining evaluation record decompose
positively, independently of whether a transition is defined elsewhere. -/
theorem run_adjoin (record word initial final : M) :
    (run g).val.Evalb ![adjoin record word, initial, final] ↔
      ∃ middle : M, g.val.Evalb ![initial, record, middle] ∧
        (run g).val.Evalb ![word, middle, final] := by
  constructor
  · intro h
    obtain ⟨states, hlen, h₀, hf, hs⟩ :=
      (run_iff_trace g (adjoin record word) initial final).mp h
    rcases nil_or_adjoin states with rfl | ⟨a, tail, rfl⟩
    · simp at hlen
    · have ha : a = initial := by simpa only [nth_adjoin_zero] using h₀
      subst a
      have hlen' : len tail = len word + 1 := by simpa using hlen
      have hg : g.val.Evalb ![initial, record, nth tail 0] := by
        simpa only [nth_adjoin_zero, nth_adjoin_succ] using hs 0 (by simp)
      refine ⟨nth tail 0, hg, (run_iff_trace g word _ final).mpr ?_⟩
      refine ⟨tail, hlen', rfl, ?_, ?_⟩
      · simpa only [len_adjoin, nth_adjoin_succ] using hf
      · intro i hi
        have h := hs (i + 1) (by simpa using hi)
        simpa only [nth_adjoin_succ] using h
  · rintro ⟨middle, hg, hr⟩
    obtain ⟨states, hlen, h₀, hf, hs⟩ := (run_iff_trace g word middle final).mp hr
    apply (run_iff_trace g (adjoin record word) initial final).mpr
    refine ⟨adjoin initial states, by simp [hlen], by simp, ?_, ?_⟩
    · simpa only [len_adjoin, nth_adjoin_succ] using hf
    · intro i hi
      rcases zero_or_succ i with rfl | ⟨i, rfl⟩
      · simpa only [nth_adjoin_zero, nth_adjoin_succ, h₀] using hg
      · simpa only [nth_adjoin_succ] using hs i (by simpa using hi)

@[simp] theorem run_singleton (record initial final : M) :
    (run g).val.Evalb ![adjoin record 0, initial, final] ↔
      g.val.Evalb ![initial, record, final] := by
  simp [run_adjoin]

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.Records
