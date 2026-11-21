/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkObservationFunctor
public import CategoricalEssentialIncompleteness.V46ForkComparison

/-! # Endpoint incompleteness for the three-point construction -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

open EffectiveFork (natCarrier)
open EnumerableCarriers (support)

/-- Every consistent c.e. extension of either endpoint theorem domain is
inseparable from its refutation domain. The extension need not be given as
a compatible family. -/
theorem endpoint_essential_incompleteness (i : Bool) (t : Idem natCarrier)
    (ht : endpointTheory i categoricalTheory ≤ t)
    (hc : t ⊓ Idem.pull (natArrow negCode negCode_computable) t = ⊥) :
    Inseparable t (Idem.pull (natArrow negCode negCode_computable) t) ∧
      t ⊔ Idem.pull (natArrow negCode negCode_computable) t ≠ ⊤ := by
  obtain ⟨ha, hb⟩ := observed_bounds i categoricalTheory le_rfl
  exact domain_incompleteness EffectiveFork.endpoint_pair_inseparable
    (natArrow atomCode atomCode_computable) (natArrow_total _ _)
    (natArrow negCode negCode_computable) (natArrow_total _ _)
    (endpointTheory i categoricalTheory) ha hb t ht hc

/-- Incompleteness holds at each endpoint of a compatible consistent family. -/
theorem endpoint_theory_incomplete (i : Bool) (t : Theory) :
    endpointTheory i t.val ⊔
      Idem.pull (natArrow negCode negCode_computable) (endpointTheory i t.val) ≠ ⊤ := by
  apply (endpoint_essential_incompleteness i (endpointTheory i t.val)
    (endpointTheory_mono i t.property.1) ?_).2
  cases i
  · exact congrArg EffectiveFork.rightIdem t.property.2.1
  · exact congrArg EffectiveFork.leftIdem t.property.2.1

/-- The endpoint's categorical noncoverage is precisely noncoverage of its
theorem and refutation sets on the numerical carrier. -/
theorem endpoint_complete_iff (t : Idem natCarrier) :
    t ⊔ Idem.pull (natArrow negCode negCode_computable) t = ⊤ ↔
      ∀ n : ℕ, n ∈ support t ∨ negCode n ∈ support t := by
  constructor
  · intro h n
    have hn : n ∈ support (t ⊔ Idem.pull (natArrow negCode negCode_computable) t) := by
      rw [h, EnumerableCarriers.support_top]
      exact Set.mem_univ n
    rw [EnumerableCarriers.support_sup] at hn
    rcases hn with hn | hn
    · exact Or.inl hn
    · right
      rw [EnumerableCarriers.support_pull] at hn
      obtain ⟨y, hy, hyt⟩ := hn
      simpa only [(mem_natArrow _ _ n y).mp hy] using hyt
  · intro h
    apply EnumerableCarriers.support_injective
    ext n
    rw [EnumerableCarriers.support_sup, EnumerableCarriers.support_top]
    constructor
    · intro _
      exact Set.mem_univ n
    · intro _
      rcases h n with hn | hn
      · exact Or.inl hn
      · right
        rw [EnumerableCarriers.support_pull]
        exact ⟨negCode n, (mem_natArrow _ _ _ _).mpr rfl, hn⟩

/-- The code-level form of the endpoint essential-incompleteness conclusion. -/
theorem endpoint_extension_has_undecidable_code (i : Bool) (t : Idem natCarrier)
    (ht : endpointTheory i categoricalTheory ≤ t)
    (hc : t ⊓ Idem.pull (natArrow negCode negCode_computable) t = ⊥) :
    ∃ n : ℕ, n ∉ support t ∧ negCode n ∉ support t := by
  classical
  have h := (endpoint_essential_incompleteness i t ht hc).2
  by_contra hn
  apply h
  apply (endpoint_complete_iff t).mpr
  intro n
  by_cases hp : n ∈ support t
  · exact Or.inl hp
  · exact Or.inr (not_not.mp (fun hneg => hn ⟨n, hp, hneg⟩))

/-- A c.e. set of endpoint sentence codes gives its restriction idempotent; consistency
and extension inclusion yield an undecidable code. -/
theorem endpoint_ce_extension_incomplete (i : Bool) (T : Set ℕ)
    (hT : REPred (· ∈ T))
    (hext : support (endpointTheory i categoricalTheory) ⊆ T)
    (hconsistent : ∀ n : ℕ, n ∈ T → negCode n ∉ T) :
    ∃ n : ℕ, n ∉ T ∧ negCode n ∉ T := by
  let t : Idem natCarrier :=
    EnumerableCarriers.relativeIdem T hT (fun _ _ => Set.mem_univ _)
  have hs : support t = T := EnumerableCarriers.support_relativeIdem _ _ _
  have ht : endpointTheory i categoricalTheory ≤ t := by
    apply (EnumerableCarriers.support_le_iff _ _).mpr
    rw [hs]
    exact hext
  have hc : t ⊓ Idem.pull (natArrow negCode negCode_computable) t = ⊥ := by
    apply EnumerableCarriers.support_injective
    ext n
    rw [EnumerableCarriers.support_inf, EnumerableCarriers.support_bot]
    constructor
    · rintro ⟨hn, hneg⟩
      rw [EnumerableCarriers.support_pull] at hneg
      obtain ⟨y, hy, hyt⟩ := hneg
      rw [(mem_natArrow _ _ _ _).mp hy] at hyt
      exact hconsistent n (hs ▸ hn) (hs ▸ hyt)
    · exact False.elim
  simpa only [hs] using endpoint_extension_has_undecidable_code i t ht hc

/-- The component conclusions of Theorem 10.5, including incompleteness of the selected
endpoint theory and the numerical pair inclusions. -/
theorem cosheaf_observation_v46 (i : Bool) (t : Theory) :
    Inseparable t.val (Idem.pull nu t.val) ∧
      (REPred (· ∈ tuplePositiveSet i t.val) ∧
        REPred (· ∈ tupleNegativeSet i t.val)) ∧
      (Disjoint (tuplePositiveSet i t.val) (tupleNegativeSet i t.val) ∧
        ¬ ∃ D : Set (ℕ × ℕ), ComputablePred (· ∈ D) ∧
          tuplePositiveSet i t.val ⊆ D ∧ Disjoint D (tupleNegativeSet i t.val)) ∧
      ({x : ℕ × ℕ | Nat.pair x.1 x.2 ∈ support EffectiveFork.endpointPair0} ⊆
          tuplePositiveSet i t.val ∧
        {x : ℕ × ℕ | Nat.pair x.1 x.2 ∈ support EffectiveFork.endpointPair1} ⊆
          tupleNegativeSet i t.val) ∧
      endpointTheory i t.val ⊔
        Idem.pull (natArrow negCode negCode_computable) (endpointTheory i t.val) ≠ ⊤ :=
  ⟨(essential_incompleteness_v46 t.val t.property.1 t.property.2.1).1,
    tuple_observations_enumerable i t.val, tuple_observations_inseparable i t,
    tuple_observed_bounds i t.val t.property.1, endpoint_theory_incomplete i t⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
