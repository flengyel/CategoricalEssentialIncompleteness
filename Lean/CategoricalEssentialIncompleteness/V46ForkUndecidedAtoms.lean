/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkAxiomClosure

/-! # Undecided atoms at the endpoints of the fork -/

@[expose] public section

open CategoryTheory
namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

open EnumerableCarriers (support)

open EffectiveFork (natCarrier)

/-- Independent c.e. theorem domains at either endpoint omit an atom with both signs. -/
theorem endpoint_undecided_atom (i : Bool) (t : Idem natCarrier)
    (ht : endpointTheory i categoricalTheory ≤ t)
    (hc : t ⊓ Idem.pull (natArrow negCode negCode_computable) t = ⊥) :
    ∃ k : ℕ, atomCode k ∉ support t ∧ negCode (atomCode k) ∉ support t := by
  classical
  let θ := natArrow atomCode atomCode_computable
  let ν := natArrow negCode negCode_computable
  let p := Idem.pull θ t
  let n := Idem.pull θ (Idem.pull ν t)
  obtain ⟨ha, hb⟩ := observed_bounds i categoricalTheory le_rfl
  have h : Inseparable p n := EffectiveFork.endpoint_pair_inseparable.enlarge
    (ha.trans (Idem.pull_mono θ ht)) (hb.trans (Idem.pull_mono θ (Idem.pull_mono ν ht)))
    (by change Idem.pull θ _ ⊓ Idem.pull θ _ = _; rw [← Idem.pull_inf, hc, Idem.pull_bot])
  have pos (k : ℕ) : k ∈ support p ↔ atomCode k ∈ support t := by
    change k ∈ support (Idem.pull θ t) ↔ _
    rw [EnumerableCarriers.support_pull]
    simp only [θ, Set.mem_ofPred_eq, mem_natArrow, exists_eq_left]
  have neg (k : ℕ) : k ∈ support n ↔ negCode (atomCode k) ∈ support t := by
    simp only [n, θ, ν, EnumerableCarriers.support_pull, Set.mem_ofPred_eq, mem_natArrow, exists_eq_left]
  by_contra! all
  have cover : p ⊔ n = ⊤ := by
    apply EnumerableCarriers.support_injective
    rw [EnumerableCarriers.support_sup, EnumerableCarriers.support_top]
    apply Set.eq_univ_of_forall
    intro k
    by_cases hk : atomCode k ∈ support t
    · exact Or.inl ((pos k).mpr hk)
    · exact Or.inr ((neg k).mpr (all k hk))
  exact h.no_separator ⟨p, n, ⟨h.disjoint, cover⟩, le_rfl, le_rfl⟩

/-- The signed atom at a component of a compatible family has the same two failures. -/
theorem exists_undecided_atom (i : Bool) (t : Idem S) (ht : categoricalTheory ≤ t)
    (hc : t ⊓ Idem.pull nu t = ⊥) :
    ∃ k : ℕ, atomCode k ∉ support (endpointTheory i t) ∧
      negCode (atomCode k) ∉ support (endpointTheory i t) := by
  apply endpoint_undecided_atom i _ (endpointTheory_mono i ht)
  cases i
  · exact congrArg EffectiveFork.rightIdem hc
  · exact congrArg EffectiveFork.leftIdem hc

open CategoricalEssentialIncompleteness.V46.ForkAxiomClosure

/-- For arbitrary c.e. endpoint axioms, the two missing sentences are literally
the atom on the selected label and its formal negation. -/
theorem axioms_undecided_atom (i : Bool) (A : Set ℕ) (hA : REPred (· ∈ A))
    (hext : support (endpointTheory i categoricalTheory) ⊆ theoremCodes A)
    (hc : ∀ p : Formula, ¬(Derives A p ∧ Derives A (.neg p))) :
    ∃ k : ℕ, ¬Derives A (.atom k) ∧ ¬Derives A (.neg (.atom k)) := by
  let t : Idem natCarrier := EnumerableCarriers.relativeIdem (theoremCodes A)
    (theoremCodes_re A hA) (fun _ _ => Set.mem_univ _)
  have hs : support t = theoremCodes A := EnumerableCarriers.support_relativeIdem _ _ _
  have ht : endpointTheory i categoricalTheory ≤ t :=
    (EnumerableCarriers.support_le_iff _ _).mpr (hs ▸ hext)
  have hcons : t ⊓ Idem.pull (natArrow negCode negCode_computable) t = ⊥ := by
    apply EnumerableCarriers.support_injective
    ext k
    simp only [EnumerableCarriers.support_inf, EnumerableCarriers.support_pull,
      EnumerableCarriers.support_bot, hs, Set.mem_inter_iff, Set.mem_ofPred_eq,
      mem_natArrow, exists_eq_left, Set.mem_empty_iff_false, iff_false]
    simpa only [theoremCodes, Set.mem_ofPred_eq, decode_negCode] using hc (Formula.decode k)
  obtain ⟨k, hp, hn⟩ := endpoint_undecided_atom i t ht hcons
  exact ⟨k, by simpa only [hs, theoremCodes, Set.mem_ofPred_eq, decode_atomCode] using hp,
    by simpa only [hs, theoremCodes, Set.mem_ofPred_eq, decode_negCode, decode_atomCode] using hn⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
