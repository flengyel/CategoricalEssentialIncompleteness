/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46Applications

/-! # Explicit endpoint application statements -/

@[expose] public section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

noncomputable section

example (i : Bool) (t : Idem EffectiveFork.natCarrier)
    (ht : endpointTheory i categoricalTheory ≤ t)
    (hc : t ⊓ Idem.pull (natArrow negCode negCode_computable) t = ⊥) :
    Inseparable t (Idem.pull (natArrow negCode negCode_computable) t) ∧
      t ⊔ Idem.pull (natArrow negCode negCode_computable) t ≠ ⊤ :=
  endpoint_essential_incompleteness i t ht hc

example (i : Bool) (t : Theory) :
    endpointTheory i t.val ⊔
      Idem.pull (natArrow negCode negCode_computable) (endpointTheory i t.val) ≠ ⊤ :=
  endpoint_theory_incomplete i t

example (t : Idem EffectiveFork.natCarrier) :
    t ⊔ Idem.pull (natArrow negCode negCode_computable) t = ⊤ ↔
      ∀ n : ℕ, n ∈ EnumerableCarriers.support t ∨
        negCode n ∈ EnumerableCarriers.support t :=
  endpoint_complete_iff t

example (i : Bool) (t : Idem EffectiveFork.natCarrier)
    (ht : endpointTheory i categoricalTheory ≤ t)
    (hc : t ⊓ Idem.pull (natArrow negCode negCode_computable) t = ⊥) :
    ∃ n : ℕ, n ∉ EnumerableCarriers.support t ∧
      negCode n ∉ EnumerableCarriers.support t :=
  endpoint_extension_has_undecidable_code i t ht hc

example (i : Bool) (T : Set ℕ) (hT : REPred (· ∈ T))
    (hext : EnumerableCarriers.support (endpointTheory i categoricalTheory) ⊆ T)
    (hc : ∀ n : ℕ, n ∈ T → negCode n ∉ T) :
    ∃ n : ℕ, n ∉ T ∧ negCode n ∉ T :=
  endpoint_ce_extension_incomplete i T hT hext hc

example (i : Bool) (t : Theory) :
    Inseparable t.val (Idem.pull nu t.val) ∧
      (REPred (· ∈ tuplePositiveSet i t.val) ∧ REPred (· ∈ tupleNegativeSet i t.val)) ∧
      (Disjoint (tuplePositiveSet i t.val) (tupleNegativeSet i t.val) ∧
        ¬ ∃ D : Set (ℕ × ℕ), ComputablePred (· ∈ D) ∧
          tuplePositiveSet i t.val ⊆ D ∧ Disjoint D (tupleNegativeSet i t.val)) ∧
      ({x : ℕ × ℕ | Nat.pair x.1 x.2 ∈ EnumerableCarriers.support EffectiveFork.endpointPair0} ⊆
          tuplePositiveSet i t.val ∧
        {x : ℕ × ℕ | Nat.pair x.1 x.2 ∈ EnumerableCarriers.support EffectiveFork.endpointPair1} ⊆
          tupleNegativeSet i t.val) ∧
      endpointTheory i t.val ⊔
        Idem.pull (natArrow negCode negCode_computable) (endpointTheory i t.val) ≠ ⊤ :=
  cosheaf_observation_v46 i t
