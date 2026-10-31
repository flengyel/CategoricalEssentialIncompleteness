/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.ForkEndpointInseparability
import CategoricalEssentialIncompleteness.ForkEssentialIncompleteness
import CategoricalEssentialIncompleteness.EnumerableInseparability

/-! # Effective endpoint observations of the actual theorem domains -/

noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

open EffectiveFork (natCarrier leftIdem rightIdem)
open EnumerableCarriers (support)

/-- `true` selects endpoint 1 and `false` selects endpoint 2. -/
def endpointTheory (i : Bool) (t : Idem S) : Idem natCarrier :=
  if i then leftIdem t else rightIdem t

def observedPositive (i : Bool) (t : Idem S) : Idem natCarrier :=
  Idem.pull (natArrow atomCode atomCode_computable) (endpointTheory i t)

def observedNegative (i : Bool) (t : Idem S) : Idem natCarrier :=
  Idem.pull (natArrow atomCode atomCode_computable)
    (Idem.pull (natArrow negCode negCode_computable) (endpointTheory i t))

theorem endpointTheory_mono (i : Bool) : Monotone (endpointTheory i) := by
  intro t t' ht
  obtain ⟨h0,h1,h2⟩ := (EffectiveFork.idem_le_iff t t').mp ht
  cases i
  · exact h2
  · exact h1

theorem observedPositive_mono (i : Bool) : Monotone (observedPositive i) :=
  fun _ _ ht => Idem.pull_mono _ (endpointTheory_mono i ht)

theorem observedNegative_mono (i : Bool) : Monotone (observedNegative i) :=
  fun _ _ ht => Idem.pull_mono _ (Idem.pull_mono _ (endpointTheory_mono i ht))

theorem observed_bounds (i : Bool) (t : Idem S) (ht : categoricalTheory ≤ t) :
    EffectiveFork.endpointPair0 ≤ observedPositive i t ∧
      EffectiveFork.endpointPair1 ≤ observedNegative i t := by
  have ha := (positive_inclusion (EffectiveFork.Recursion.toIdem EffectiveFork.Recursion.pair0)
    (EffectiveFork.Recursion.toIdem EffectiveFork.Recursion.pair1)).trans (Idem.pull_mono theta ht)
  have hb := (negative_inclusion (EffectiveFork.Recursion.toIdem EffectiveFork.Recursion.pair0)
    (EffectiveFork.Recursion.toIdem EffectiveFork.Recursion.pair1)).trans
      (Idem.pull_mono theta (Idem.pull_mono nu ht))
  obtain ⟨_,ha1,ha2⟩ := (EffectiveFork.idem_le_iff _ _).mp ha
  obtain ⟨_,hb1,hb2⟩ := (EffectiveFork.idem_le_iff _ _).mp hb
  cases i
  · exact ⟨EffectiveFork.right_pair0 ▸ ha2,EffectiveFork.right_pair1 ▸ hb2⟩
  · exact ⟨EffectiveFork.left_pair0 ▸ ha1,EffectiveFork.left_pair1 ▸ hb1⟩

theorem observed_disjoint (i : Bool) (t : Idem S) (hc : t ⊓ Idem.pull nu t=⊥) :
    observedPositive i t ⊓ observedNegative i t=⊥ := by
  have he : endpointTheory i t ⊓
      Idem.pull (natArrow negCode negCode_computable) (endpointTheory i t)=⊥ := by
    cases i
    · exact congrArg rightIdem hc
    · exact congrArg leftIdem hc
  change Idem.pull _ _ ⊓ Idem.pull _ _=⊥
  rw [← Idem.pull_inf,he,Idem.pull_bot]

theorem observed_inseparable (i : Bool) (t : Idem S) (ht : categoricalTheory ≤ t)
    (hc : t ⊓ Idem.pull nu t=⊥) : Inseparable (observedPositive i t) (observedNegative i t) :=
  EffectiveFork.endpoint_pair_inseparable.enlarge (observed_bounds i t ht).1
    (observed_bounds i t ht).2 (observed_disjoint i t hc)

theorem observed_recursivelyInseparable (i : Bool) (t : Idem S) (ht : categoricalTheory ≤ t)
    (hc : t ⊓ Idem.pull nu t=⊥) :
    Numerical.RecursivelyInseparable (support (observedPositive i t))
      (support (observedNegative i t)) :=
  EnumerableCarriers.supports_recursivelyInseparable (observed_inseparable i t ht hc)

theorem observed_enumerable (i : Bool) (t : Idem S) :
    REPred (· ∈ support (observedPositive i t)) ∧ REPred (· ∈ support (observedNegative i t)) :=
  ⟨EnumerableCarriers.support_re _,EnumerableCarriers.support_re _⟩

theorem observedPositive_mem (i : Bool) (t : Idem S) (x : ℕ) :
    x ∈ support (observedPositive i t) ↔ atomCode x ∈ support (endpointTheory i t) := by
  rw [observedPositive,EnumerableCarriers.support_pull]
  simp only [Set.mem_setOf_eq,mem_natArrow,exists_eq_left]

theorem observedNegative_mem (i : Bool) (t : Idem S) (x : ℕ) :
    x ∈ support (observedNegative i t) ↔ negCode (atomCode x) ∈ support (endpointTheory i t) := by
  rw [observedNegative,EnumerableCarriers.support_pull]
  simp only [Set.mem_setOf_eq,mem_natArrow,exists_eq_left]
  rw [EnumerableCarriers.support_pull]
  simp only [Set.mem_setOf_eq,mem_natArrow,exists_eq_left]

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
