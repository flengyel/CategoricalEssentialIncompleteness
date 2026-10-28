/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import Arith.Feferman.ProofFormula
import Foundation.FirstOrder.Arithmetic.HFS.PRF
import Foundation.FirstOrder.Arithmetic.HFS.Vec
import Metamath.Feferman.ProofCode
import Foundation.FirstOrder.Arithmetic.R0.Representation

/-!
# A structural arithmetic formula for Feferman proof sequences

This module arithmetizes the existing numerical predicate
`Metamath.Feferman.Proof_T` by spelling out its decoder, line checker, and final
line condition. Unlike the selected formula `proofTFormula`, the resulting
`proofGraph` supports reasoning in arbitrary models of `𝗜𝗺𝞺₁`. This gives the
closed PA theorem `provable_PA_uniformMPClosure`.

The numerical proof predicate and its encodings are unchanged. This module is
in the upper `Arith` layer because its formulas use Foundation; the lower
`Metamath` layer remains independent of Foundation.
-/

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open Metamath.Feferman

set_option linter.flexible false

namespace Arith.Feferman.Structural

noncomputable def spreadDef : 𝚺₀.Semisentence 2 := .mkSigma
  “y n. ∀ x < y + 2 * n + 1, (x ∈ y ↔ ∃ i ∈' n, x = 2 * i)”

noncomputable def codePairGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y a b. ∃ s, ∃ t, !spreadDef s a ∧ !spreadDef t b ∧ y = s + 2 * t”

section Model

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def IsSpread (y n : V) : Prop := ∀ x : V, x ∈ y ↔ ∃ i ∈ n, x = 2 * i

private lemma lt_bound_of_lt_left {x y n : V} (h : x < y) : x < y + 2 * n + 1 :=
  calc x < y := h
    _ ≤ y + 2 * n := by simp
    _ < y + 2 * n + 1 := by simp

private lemma lt_bound_of_lt_right {i n y : V} (h : i < n) : 2 * i < y + 2 * n + 1 :=
  calc (2 : V) * i ≤ 2 * n := by gcongr
    _ ≤ y + 2 * n := by simp
    _ < y + 2 * n + 1 := by simp

lemma spreadDef_iff (y n : V) :
    Semiformula.Evalb (M := V) ![y, n] spreadDef.val ↔ IsSpread y n := by
  simp [spreadDef, IsSpread]
  constructor
  · intro h x
    constructor
    · intro hx
      exact (h x (lt_bound_of_lt_left (lt_of_mem hx))).mp hx
    · rintro ⟨i, hi, rfl⟩
      exact (h (2 * i) (lt_bound_of_lt_right (lt_of_mem hi))).mpr ⟨i, hi, rfl⟩
  · intro h x _
    exact h x

lemma isSpread_existsUnique (n : V) : ∃! y : V, IsSpread y n := by
  have hfun : 𝚺₁-Function₁ (fun i : V => 2 * i) := by definability
  simpa [IsSpread] using sigma₁_replacement hfun n

lemma codePairGraph_iff (y a b : V) :
    Semiformula.Evalb (M := V) ![y, a, b] codePairGraph.val ↔
      ∃ s t : V, IsSpread s a ∧ IsSpread t b ∧ y = s + 2 * t := by
  simp [codePairGraph, spreadDef_iff]

end Model

/-! ### Predecessor, from the pinned theorem -/

theorem nonzero_eq_succ
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {x : V} (hx : x ≠ 0) :
    ∃ y : V, x = y + 1 :=
  exists_succ_of_ne_zero hx

section Recurrences

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private lemma two_mul_succ (i : V) : 2 * (i + 1) = (2 * i + 1) + 1 :=
  calc 2 * (i + 1) = 2 * i + 2 * 1 := by rw [mul_add]
    _ = 2 * i + 2 := by rw [mul_one]
    _ = 2 * i + (1 + 1) := by rw [one_add_one_eq_two]
    _ = (2 * i + 1) + 1 := (add_assoc _ _ _).symm

theorem isSpread_double
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {s a : V} (h : IsSpread s a) :
    IsSpread (2 * (2 * s)) (2 * a) := by
  intro x
  constructor
  · intro hx
    have hx0 : x ≠ 0 := by rintro rfl; exact absurd hx (by simp)
    obtain ⟨j, rfl⟩ := nonzero_eq_succ hx0
    have hj : j ∈ 2 * s := succ_mem_two_mul_iff.mp hx
    have hj0 : j ≠ 0 := by rintro rfl; exact absurd hj (by simp)
    obtain ⟨k, rfl⟩ := nonzero_eq_succ hj0
    obtain ⟨i, hi, rfl⟩ := (h k).mp (succ_mem_two_mul_iff.mp hj)
    exact ⟨i + 1, succ_mem_two_mul_iff.mpr hi, (two_mul_succ i).symm ▸ rfl⟩
  · rintro ⟨i, hi, rfl⟩
    have hi0 : i ≠ 0 := by rintro rfl; exact absurd hi (by simp)
    obtain ⟨i0, rfl⟩ := nonzero_eq_succ hi0
    have hi0a : i0 ∈ a := succ_mem_two_mul_iff.mp hi
    rw [two_mul_succ i0]
    exact succ_mem_two_mul_iff.mpr
      (succ_mem_two_mul_iff.mpr ((h (2 * i0)).mpr ⟨i0, hi0a, rfl⟩))

theorem isSpread_double_add_one
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {s a : V} (h : IsSpread s a) :
    IsSpread (2 * (2 * s) + 1) (2 * a + 1) := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx0
  · constructor
    · intro _
      exact ⟨0, by simp, by rw [mul_zero]⟩
    · intro _
      simp
  · obtain ⟨j, rfl⟩ := nonzero_eq_succ hx0
    constructor
    · intro hx
      have hj : j ∈ 2 * s := succ_mem_two_mul_succ_iff.mp hx
      have hj0 : j ≠ 0 := by rintro rfl; exact absurd hj (by simp)
      obtain ⟨k, rfl⟩ := nonzero_eq_succ hj0
      obtain ⟨i, hi, rfl⟩ := (h k).mp (succ_mem_two_mul_iff.mp hj)
      exact ⟨i + 1, succ_mem_two_mul_succ_iff.mpr hi, (two_mul_succ i).symm ▸ rfl⟩
    · rintro ⟨i, hi, hx⟩
      have hi0 : i ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hx
        simp at hx
      obtain ⟨i0, rfl⟩ := nonzero_eq_succ hi0
      have hi0a : i0 ∈ a := succ_mem_two_mul_succ_iff.mp hi
      rw [two_mul_succ i0] at hx
      have hj : j = 2 * i0 + 1 := add_right_cancel hx
      subst hj
      exact succ_mem_two_mul_succ_iff.mpr
        (succ_mem_two_mul_iff.mpr ((h (2 * i0)).mpr ⟨i0, hi0a, rfl⟩))

end Recurrences


/-! ### Zero laws -/

section Peeling

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private lemma isSpread_zero : IsSpread (0 : V) 0 := by
  intro x; simp

theorem isSpread_eq_zero_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {s a : V}
    (h : IsSpread s a) :
    s = 0 ↔ a = 0 := by
  constructor
  · -- `s = 0` has no members, so `a` can have none either.
    rintro rfl
    refine mem_ext ?_
    intro i
    constructor
    · intro hi
      exact absurd ((h (2 * i)).mpr ⟨i, hi, rfl⟩) (by simp)
    · intro hi
      exact absurd hi (by simp)
  · -- `a = 0` forces `s` to be the empty spread, which is unique.
    rintro rfl
    exact (isSpread_existsUnique (0 : V)).unique h isSpread_zero

theorem codePairGraph_zero_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a b : V) :
    Semiformula.Evalb (M := V)
      ![(0 : V), a, b] codePairGraph.val ↔
    a = 0 ∧ b = 0 := by
  rw [codePairGraph_iff]
  constructor
  · rintro ⟨s, t, hs, ht, hn⟩
    -- `0 = s + 2 * t` forces both summands to vanish, in the ordered semiring.
    have hs0 : s = 0 := by
      have hle : s ≤ s + 2 * t := by simp
      rw [← hn] at hle
      simpa using hle
    have ht0 : t = 0 := by
      have hle : 2 * t ≤ s + 2 * t := by simp
      rw [← hn] at hle
      have h2 : 2 * t = 0 := by simpa using hle
      have := div_mul_right t (b := 2) (by simp)
      rw [h2] at this
      simpa using this.symm
    exact ⟨(isSpread_eq_zero_iff hs).mp hs0, (isSpread_eq_zero_iff ht).mp ht0⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨0, 0, isSpread_zero, isSpread_zero, by simp⟩

/-! ### Parity peeling -/

/-- Identify the spread of `a` when `a` is even. -/
private lemma spread_of_even {s a c u : V}
    (hs : IsSpread s a) (hu : IsSpread u c) (hac : a = 2 * c) :
    s = 2 * (2 * u) :=
  (isSpread_existsUnique a).unique hs (by rw [hac]; exact isSpread_double hu)

/-- Identify the spread of `a` when `a` is odd. -/
private lemma spread_of_odd {s a c u : V}
    (hs : IsSpread s a) (hu : IsSpread u c) (hac : a = 2 * c + 1) :
    s = 2 * (2 * u) + 1 :=
  (isSpread_existsUnique a).unique hs (by rw [hac]; exact isSpread_double_add_one hu)

/-- Halving a normalized even equality. -/
private lemma eq_of_two_mul_eq {x w : V} (h : 2 * x = 2 * w) : x = w :=
  calc x = (2 * x) / 2 := (div_mul_right x (by simp)).symm
    _ = (2 * w) / 2 := by rw [h]
    _ = w := div_mul_right _ (by simp)

/-- An even value cannot equal an odd one; the contradiction is drawn inside the
model, by applying the residue map and reducing with the pinned modulo
lemmas. -/
private lemma even_ne_odd {x w : V} (h : 2 * x = 2 * w + 1) : False := by
  have hmod : (2 * x) % 2 = (2 * w + 1) % 2 := congrArg (fun q : V => q % 2) h
  rw [mod_mul_self_right x 2,
    mod_add_remove_left_of_dvd (Dvd.intro w rfl) (by simp)] at hmod
  simp at hmod

private lemma norm_even (u t : V) : 2 * (2 * u) + 2 * t = 2 * (t + 2 * u) := by
  rw [mul_add]; exact add_comm _ _

private lemma norm_odd (u t : V) :
    2 * (2 * u) + 1 + 2 * t = 2 * (t + 2 * u) + 1 :=
  calc 2 * (2 * u) + 1 + 2 * t = 2 * (2 * u) + (1 + 2 * t) := add_assoc _ _ _
    _ = 2 * (2 * u) + (2 * t + 1) := by rw [add_comm 1 (2 * t)]
    _ = 2 * (2 * u) + 2 * t + 1 := (add_assoc _ _ _).symm
    _ = 2 * (t + 2 * u) + 1 := by rw [norm_even]

theorem codePairGraph_two_mul_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (x a b : V) :
    Semiformula.Evalb (M := V)
      ![2 * x, a, b] codePairGraph.val ↔
    ∃ c : V,
      a = 2 * c ∧
      Semiformula.Evalb (M := V)
        ![x, b, c] codePairGraph.val := by
  rw [codePairGraph_iff]
  constructor
  · rintro ⟨s, t, hs, ht, hn⟩
    obtain ⟨u, hu, -⟩ := isSpread_existsUnique (a / 2)
    rcases even_or_odd' a with ha | ha
    · refine ⟨a / 2, ha, ?_⟩
      rw [codePairGraph_iff]
      refine ⟨t, u, ht, hu, ?_⟩
      refine eq_of_two_mul_eq ?_
      rw [hn, spread_of_even hs hu ha]
      exact norm_even u t
    · exfalso
      have h1 : 2 * x = 2 * (t + 2 * u) + 1 := by
        rw [hn, spread_of_odd hs hu ha]; exact norm_odd u t
      exact even_ne_odd h1
  · rintro ⟨c, hac, hchild⟩
    obtain ⟨s', t', hs', ht', hx⟩ := (codePairGraph_iff x b c).mp hchild
    refine ⟨2 * (2 * t'), s', ?_, hs', ?_⟩
    · rw [hac]; exact isSpread_double ht'
    · rw [hx, ← norm_even t' s']

theorem codePairGraph_two_mul_add_one_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (x a b : V) :
    Semiformula.Evalb (M := V)
      ![2 * x + 1, a, b] codePairGraph.val ↔
    ∃ c : V,
      a = 2 * c + 1 ∧
      Semiformula.Evalb (M := V)
        ![x, b, c] codePairGraph.val := by
  rw [codePairGraph_iff]
  constructor
  · rintro ⟨s, t, hs, ht, hn⟩
    obtain ⟨u, hu, -⟩ := isSpread_existsUnique (a / 2)
    rcases even_or_odd' a with ha | ha
    · exfalso
      have h1 : 2 * x + 1 = 2 * (t + 2 * u) := by
        rw [hn, spread_of_even hs hu ha]; exact norm_even u t
      exact even_ne_odd h1.symm
    · refine ⟨a / 2, ha, ?_⟩
      rw [codePairGraph_iff]
      refine ⟨t, u, ht, hu, ?_⟩
      refine eq_of_two_mul_eq ?_
      have h1 : 2 * x + 1 = 2 * (t + 2 * u) + 1 := by
        rw [hn, spread_of_odd hs hu ha]; exact norm_odd u t
      exact add_right_cancel h1
  · rintro ⟨c, hac, hchild⟩
    obtain ⟨s', t', hs', ht', hx⟩ := (codePairGraph_iff x b c).mp hchild
    refine ⟨2 * (2 * t') + 1, s', ?_, hs', ?_⟩
    · rw [hac]; exact isSpread_double_add_one ht'
    · rw [hx, ← norm_odd t' s']

end Peeling


/-! ### The bounded relation and the uniqueness predicate -/

section Injectivity

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The bounded matrix of `spreadDef`, copied from B6R1. Bounded quantifiers
only, so the definability machinery handles it directly. -/
def SpreadB (y n : V) : Prop :=
  ∀ x < y + 2 * n + 1,
    (x ∈ y ↔ ∃ i < n, i ∈ n ∧ x = 2 * i)

/-- `SpreadB` and the unbounded `IsSpread` agree, copied from B6R1. -/
lemma spreadB_iff (y n : V) : SpreadB y n ↔ IsSpread y n := by
  constructor
  · intro h x
    constructor
    · intro hx
      obtain ⟨i, _, hi, rfl⟩ := (h x (lt_bound_of_lt_left (lt_of_mem hx))).mp hx
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact (h (2 * i) (lt_bound_of_lt_right (lt_of_mem hi))).mpr ⟨i, lt_of_mem hi, hi, rfl⟩
  · intro h x _
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := (h x).mp hx
      exact ⟨i, lt_of_mem hi, hi, rfl⟩
    · rintro ⟨i, _, hi, rfl⟩
      exact (h (2 * i)).mpr ⟨i, hi, rfl⟩

/-- Uniqueness of the decoded pair at a fixed output, with every spread witness
exposed universally so that the predicate stays `𝚷₁`. -/
def UniqueAt (y : V) : Prop :=
  ∀ a b s t a' b' s' t' : V,
    SpreadB s a →
    SpreadB t b →
    y = s + 2 * t →
    SpreadB s' a' →
    SpreadB t' b' →
    y = s' + 2 * t' →
    a = a' ∧ b = b'

/-- `SpreadB` is registered once as a `𝚺₀` relation, so that the definability
search treats it atomically inside `UniqueAt` instead of re-deriving it at each
of its four occurrences. -/
instance spreadB_definable : 𝚺₀-Relation (SpreadB : V → V → Prop) := by
  unfold SpreadB; definability

end Injectivity

theorem uniqueAt_pi1
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    𝚷₁-Predicate (UniqueAt (V := V)) := by
  unfold UniqueAt
  definability

theorem uniqueAt_iff_codePairGraph
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y : V) :
    UniqueAt (V := V) y ↔
      ∀ a b a' b' : V,
        Semiformula.Evalb (M := V)
          ![y, a, b] codePairGraph.val →
        Semiformula.Evalb (M := V)
          ![y, a', b'] codePairGraph.val →
        a = a' ∧ b = b' := by
  constructor
  · intro hU a b a' b' h h'
    obtain ⟨s, t, hs, ht, hn⟩ := (codePairGraph_iff y a b).mp h
    obtain ⟨s', t', hs', ht', hn'⟩ := (codePairGraph_iff y a' b').mp h'
    exact hU a b s t a' b' s' t'
      ((spreadB_iff s a).mpr hs) ((spreadB_iff t b).mpr ht) hn
      ((spreadB_iff s' a').mpr hs') ((spreadB_iff t' b').mpr ht') hn'
  · intro hG a b s t a' b' s' t' hs ht hn hs' ht' hn'
    refine hG a b a' b' ?_ ?_
    · exact (codePairGraph_iff y a b).mpr
        ⟨s, t, (spreadB_iff s a).mp hs, (spreadB_iff t b).mp ht, hn⟩
    · exact (codePairGraph_iff y a' b').mpr
        ⟨s', t', (spreadB_iff s' a').mp hs', (spreadB_iff t' b').mp ht', hn'⟩

/-- The whole of the all-model content, by internal `𝚷₁` polynomial induction on
the output. The nonstandard case is covered by this induction; no external
recursion on the standard natural numbers is involved. -/
private theorem uniqueAt_all
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y : V) :
    UniqueAt (V := V) y := by
  induction y using pi1_polynomial_induction with
  | hP => exact uniqueAt_pi1
  | zero =>
    refine (uniqueAt_iff_codePairGraph (0 : V)).mpr ?_
    intro a b a' b' h h'
    obtain ⟨ha, hb⟩ := (codePairGraph_zero_iff a b).mp h
    obtain ⟨ha', hb'⟩ := (codePairGraph_zero_iff a' b').mp h'
    exact ⟨by rw [ha, ha'], by rw [hb, hb']⟩
  | even x _ ih =>
    refine (uniqueAt_iff_codePairGraph (2 * x)).mpr ?_
    intro a b a' b' h h'
    obtain ⟨c, hac, hc⟩ := (codePairGraph_two_mul_iff x a b).mp h
    obtain ⟨c', hac', hc'⟩ := (codePairGraph_two_mul_iff x a' b').mp h'
    -- the child result has order `b = b' ∧ c = c'`
    obtain ⟨hbb, hcc⟩ := (uniqueAt_iff_codePairGraph x).mp ih b c b' c' hc hc'
    exact ⟨by rw [hac, hac', hcc], hbb⟩
  | odd x ih =>
    refine (uniqueAt_iff_codePairGraph (2 * x + 1)).mpr ?_
    intro a b a' b' h h'
    obtain ⟨c, hac, hc⟩ := (codePairGraph_two_mul_add_one_iff x a b).mp h
    obtain ⟨c', hac', hc'⟩ := (codePairGraph_two_mul_add_one_iff x a' b').mp h'
    obtain ⟨hbb, hcc⟩ := (uniqueAt_iff_codePairGraph x).mp ih b c b' c' hc hc'
    exact ⟨by rw [hac, hac', hcc], hbb⟩

theorem codePairGraph_injective
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {y a b a' b' : V}
    (h :
      Semiformula.Evalb (M := V)
        ![y, a, b] codePairGraph.val)
    (h' :
      Semiformula.Evalb (M := V)
        ![y, a', b'] codePairGraph.val) :
    a = a' ∧ b = b' :=
  (uniqueAt_iff_codePairGraph y).mp (uniqueAt_all y) a b a' b' h h'


section Surjectivity

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private lemma surjective_aux (n : V) :
    ∃ a b s t : V, SpreadB s a ∧ SpreadB t b ∧ n = s + 2 * t := by
  induction n using sigma1_polynomial_induction with
  | hP => definability
  | zero =>
    exact ⟨0, 0, 0, 0, (spreadB_iff 0 0).mpr (by intro x; simp),
      (spreadB_iff 0 0).mpr (by intro x; simp), by simp⟩
  | even x _ ih =>
    obtain ⟨a, b, s, t, hs, ht, hn⟩ := ih
    refine ⟨2 * b, a, 2 * (2 * t), s, (spreadB_iff _ _).mpr ?_,
      (spreadB_iff _ _).mpr ((spreadB_iff _ _).mp hs), ?_⟩
    · exact isSpread_double ((spreadB_iff _ _).mp ht)
    · calc 2 * x = 2 * (s + 2 * t) := by rw [hn]
        _ = 2 * s + 2 * (2 * t) := by rw [mul_add]
        _ = 2 * (2 * t) + 2 * s := add_comm _ _
  | odd x ih =>
    obtain ⟨a, b, s, t, hs, ht, hn⟩ := ih
    refine ⟨2 * b + 1, a, 2 * (2 * t) + 1, s, (spreadB_iff _ _).mpr ?_,
      (spreadB_iff _ _).mpr ((spreadB_iff _ _).mp hs), ?_⟩
    · exact isSpread_double_add_one ((spreadB_iff _ _).mp ht)
    · calc 2 * x + 1 = 2 * (s + 2 * t) + 1 := by rw [hn]
        _ = (2 * s + 2 * (2 * t)) + 1 := by rw [mul_add]
        _ = (2 * (2 * t) + 2 * s) + 1 := by rw [add_comm (2 * s)]
        _ = 2 * (2 * t) + (2 * s + 1) := add_assoc _ _ _
        _ = 2 * (2 * t) + (1 + 2 * s) := by rw [add_comm (2 * s) 1]
        _ = (2 * (2 * t) + 1) + 2 * s := (add_assoc _ _ _).symm

end Surjectivity

theorem codePairGraph_surjective
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (n : V) :
    ∃ a b : V,
      Semiformula.Evalb (M := V)
        ![n, a, b] codePairGraph.val := by
  obtain ⟨a, b, s, t, hs, ht, hn⟩ := surjective_aux n
  exact ⟨a, b, (codePairGraph_iff n a b).mpr
    ⟨s, t, (spreadB_iff s a).mp hs, (spreadB_iff t b).mp ht, hn⟩⟩


section Standard

private lemma nat_succ_mem_iff (i a : ℕ) : i + 1 ∈ a ↔ i ∈ a / 2 := by
  rw [succ_mem_iff_mem_div_two]
  refine Iff.of_eq (congrArg (fun t : ℕ => i ∈ t) ?_)
  refine div_eq_of (V := ℕ) (b := 2) (a := a) (c := a / 2) ?_ ?_
  · rw [le_def]; omega
  · omega

private lemma nat_zero_mem_iff (a : ℕ) : (0:ℕ) ∈ a ↔ a % 2 = 1 := by
  have h : (0:ℕ) ∈ a ↔ ¬ (2 ∣ a) := (zero_mem_iff (V := ℕ) (a := a)).symm.not_left.symm
  rw [h]; omega

private lemma nat_isSpread_bitSpread (n : ℕ) : IsSpread (bitSpread n) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x
    have hrec : bitSpread n = n % 2 + 4 * bitSpread (n / 2) := bitSpread_eq n
    match x with
    | 0 =>
      rw [nat_zero_mem_iff, hrec]
      constructor
      · intro h
        exact ⟨0, by rw [nat_zero_mem_iff]; omega, by omega⟩
      · rintro ⟨i, hi, hzero⟩
        have : i = 0 := by omega
        subst this
        rw [nat_zero_mem_iff] at hi
        omega
    | 1 =>
      rw [nat_succ_mem_iff, nat_zero_mem_iff, hrec]
      constructor
      · intro h; exfalso; omega
      · rintro ⟨i, hi, hone⟩; omega
    | (j + 2) =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp only [bitSpread_zero] at hrec ⊢
        constructor
        · intro h
          rw [hrec] at h
          simp at h
        · rintro ⟨i, hi, _⟩
          exact absurd hi (by simp)
      · have hhalf : bitSpread n / 2 / 2 = bitSpread (n / 2) := by
          rw [hrec]; omega
        rw [show j + 2 = (j + 1) + 1 from rfl, nat_succ_mem_iff, nat_succ_mem_iff, hhalf]
        rw [ih (n / 2) (by omega) j]
        constructor
        · rintro ⟨i, hi, hj⟩
          exact ⟨i + 1, (nat_succ_mem_iff i n).mpr hi, by omega⟩
        · rintro ⟨i, hi, hj⟩
          refine ⟨i - 1, ?_, by omega⟩
          have hii : i = (i - 1) + 1 := by omega
          rw [hii] at hi
          exact (nat_succ_mem_iff (i - 1) n).mp hi

private lemma nat_isSpread_iff (s n : ℕ) : IsSpread s n ↔ s = bitSpread n := by
  constructor
  · intro h
    exact (isSpread_existsUnique (V := ℕ) n).unique h (nat_isSpread_bitSpread n)
  · rintro rfl
    exact nat_isSpread_bitSpread n

end Standard

theorem codePairGraph_nat_iff
    (y a b : ℕ) :
    Semiformula.Evalb (M := ℕ) ![y, a, b] codePairGraph.val ↔
      y = Metamath.Feferman.codePair a b := by
  rw [codePairGraph_iff]
  constructor
  · rintro ⟨s, t, hs, ht, rfl⟩
    rw [nat_isSpread_iff] at hs ht
    rw [hs, ht, Metamath.Feferman.codePair]
    rfl
  · rintro rfl
    exact ⟨bitSpread a, bitSpread b, nat_isSpread_bitSpread a, nat_isSpread_bitSpread b,
      by rw [Metamath.Feferman.codePair]; rfl⟩



/-! ### The fixed inverse formula -/

noncomputable def codeUnpairGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “a b n. ∃ s, ∃ t, !spreadDef s a ∧ !spreadDef t b ∧ n = s + 2 * t”

theorem codeUnpairGraph_iff_codePairGraph
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a b n : V) :
    Semiformula.Evalb (M := V)
      ![a, b, n] codeUnpairGraph.val ↔
    Semiformula.Evalb (M := V)
      ![n, a, b] codePairGraph.val := by
  simp [codeUnpairGraph, codePairGraph]

theorem codeUnpairGraph_existsUnique
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (n : V) :
    ∃! p : V × V,
      Semiformula.Evalb (M := V)
        ![p.1, p.2, n] codeUnpairGraph.val := by
  -- existence, from the copied surjectivity theorem
  obtain ⟨a, b, hab⟩ := codePairGraph_surjective n
  refine ⟨(a, b), (codeUnpairGraph_iff_codePairGraph a b n).mpr hab, ?_⟩
  -- uniqueness, from the copied injectivity theorem
  intro p hp
  have hp' := (codeUnpairGraph_iff_codePairGraph p.1 p.2 n).mp hp
  obtain ⟨h1, h2⟩ := codePairGraph_injective hp' hab
  exact Prod.ext h1 h2

theorem codeUnpairGraph_nat_iff
    (a b n : ℕ) :
    Semiformula.Evalb (M := ℕ)
      ![a, b, n] codeUnpairGraph.val ↔
    (a, b) = Metamath.Feferman.codeUnpair n := by
  rw [codeUnpairGraph_iff_codePairGraph, codePairGraph_nat_iff]
  constructor
  · rintro rfl
    exact (Metamath.Feferman.codeUnpair_codePair a b).symm
  · intro h
    have hp := Metamath.Feferman.codePair_codeUnpair n
    rw [← h] at hp
    exact hp.symm


/-! ### The fixed coordinate formulas -/

noncomputable def codeUnpairFstGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “a n. ∃ b, !codeUnpairGraph a b n”

noncomputable def codeUnpairSndGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “b n. ∃ a, !codeUnpairGraph a b n”

/-! ### Evaluator bridges

These fix the variable order once. Every consumer theorem below goes through
them, so no later proof unfolds the quotation semantics of a coordinate formula
on its own. -/

theorem codeUnpairFstGraph_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a n : V) :
    Semiformula.Evalb (M := V)
      ![a, n] codeUnpairFstGraph.val ↔
    ∃ b : V,
      Semiformula.Evalb (M := V)
        ![a, b, n] codeUnpairGraph.val := by
  simp [codeUnpairFstGraph]

theorem codeUnpairSndGraph_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (b n : V) :
    Semiformula.Evalb (M := V)
      ![b, n] codeUnpairSndGraph.val ↔
    ∃ a : V,
      Semiformula.Evalb (M := V)
        ![a, b, n] codeUnpairGraph.val := by
  simp [codeUnpairSndGraph]

/-! ### All-model unique existence for each coordinate -/

theorem codeUnpairFstGraph_existsUnique
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (n : V) :
    ∃! a : V,
      Semiformula.Evalb (M := V)
        ![a, n] codeUnpairFstGraph.val := by
  obtain ⟨p, hp, hpu⟩ := codeUnpairGraph_existsUnique (V := V) n
  refine ⟨p.1, (codeUnpairFstGraph_iff p.1 n).mpr ⟨p.2, hp⟩, ?_⟩
  intro a ha
  obtain ⟨b, hab⟩ := (codeUnpairFstGraph_iff a n).mp ha
  exact congrArg Prod.fst (hpu (a, b) hab)

theorem codeUnpairSndGraph_existsUnique
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (n : V) :
    ∃! b : V,
      Semiformula.Evalb (M := V)
        ![b, n] codeUnpairSndGraph.val := by
  obtain ⟨p, hp, hpu⟩ := codeUnpairGraph_existsUnique (V := V) n
  refine ⟨p.2, (codeUnpairSndGraph_iff p.2 n).mpr ⟨p.1, hp⟩, ?_⟩
  intro b hb
  obtain ⟨a, hab⟩ := (codeUnpairSndGraph_iff b n).mp hb
  exact congrArg Prod.snd (hpu (a, b) hab)

/-! ### Standard-model agreement for each coordinate -/

theorem codeUnpairFstGraph_nat_iff
    (a n : ℕ) :
    Semiformula.Evalb (M := ℕ)
      ![a, n] codeUnpairFstGraph.val ↔
    a = (Metamath.Feferman.codeUnpair n).1 := by
  rw [codeUnpairFstGraph_iff]
  constructor
  · rintro ⟨b, hb⟩
    exact congrArg Prod.fst ((codeUnpairGraph_nat_iff a b n).mp hb)
  · intro h
    exact ⟨(Metamath.Feferman.codeUnpair n).2,
      (codeUnpairGraph_nat_iff a _ n).mpr (Prod.ext h rfl)⟩

theorem codeUnpairSndGraph_nat_iff
    (b n : ℕ) :
    Semiformula.Evalb (M := ℕ)
      ![b, n] codeUnpairSndGraph.val ↔
    b = (Metamath.Feferman.codeUnpair n).2 := by
  rw [codeUnpairSndGraph_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact congrArg Prod.snd ((codeUnpairGraph_nat_iff a b n).mp ha)
  · intro h
    exact ⟨(Metamath.Feferman.codeUnpair n).1,
      (codeUnpairGraph_nat_iff _ b n).mpr (Prod.ext rfl h)⟩


/-! ### All-model descent bound for the second coordinate

The project's `codeUnpair_right_le` is a statement about standard `ℕ` only, and
is source context here rather than a proof step. The bound below is established
inside an arbitrary `𝗜𝚺₁`-model by internal `𝚷₁` polynomial induction. -/

section Descent

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `t ≤ 2 * t`, proved explicitly rather than left to simplification. -/
private lemma self_le_two_mul (t : V) : t ≤ 2 * t :=
  calc t ≤ t + t := by simp
    _ = 2 * t := (two_mul t).symm

end Descent

def SpreadDominates
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a : V) : Prop :=
  ∀ s : V, SpreadB s a → a ≤ s

theorem spreadDominates_pi1
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    𝚷₁-Predicate (SpreadDominates (V := V)) := by
  unfold SpreadDominates
  definability

theorem spreadDominates_all
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a : V) :
    SpreadDominates (V := V) a := by
  induction a using pi1_polynomial_induction with
  | hP => exact spreadDominates_pi1
  | zero =>
    intro s _
    simp
  | even x _ ih =>
    intro s hs
    -- the canonical spread of `x`, and the induction hypothesis at it
    obtain ⟨t, ht, -⟩ := isSpread_existsUnique (V := V) x
    have hxt : x ≤ t := ih t ((spreadB_iff t x).mpr ht)
    -- the arbitrary spread of `2 * x` is the canonical one
    have hcanon : IsSpread (2 * (2 * t)) (2 * x) := isSpread_double ht
    have hseq : s = 2 * (2 * t) :=
      (isSpread_existsUnique (2 * x)).unique ((spreadB_iff s (2 * x)).mp hs) hcanon
    rw [hseq]
    calc 2 * x ≤ 2 * t := by gcongr
      _ ≤ 2 * (2 * t) := by gcongr; exact self_le_two_mul t
  | odd x ih =>
    intro s hs
    obtain ⟨t, ht, -⟩ := isSpread_existsUnique (V := V) x
    have hxt : x ≤ t := ih t ((spreadB_iff t x).mpr ht)
    have hcanon : IsSpread (2 * (2 * t) + 1) (2 * x + 1) := isSpread_double_add_one ht
    have hseq : s = 2 * (2 * t) + 1 :=
      (isSpread_existsUnique (2 * x + 1)).unique ((spreadB_iff s (2 * x + 1)).mp hs) hcanon
    rw [hseq]
    have hle : 2 * x ≤ 2 * (2 * t) :=
      calc 2 * x ≤ 2 * t := by gcongr
        _ ≤ 2 * (2 * t) := by gcongr; exact self_le_two_mul t
    gcongr

theorem isSpread_input_le
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {s a : V}
    (h : IsSpread s a) :
    a ≤ s :=
  spreadDominates_all a s ((spreadB_iff s a).mpr h)

theorem codePairGraph_right_le
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {n a b : V}
    (h :
      Semiformula.Evalb (M := V)
        ![n, a, b] codePairGraph.val) :
    b ≤ n := by
  obtain ⟨s, t, hs, ht, hn⟩ := (codePairGraph_iff n a b).mp h
  calc b ≤ t := isSpread_input_le ht
    _ ≤ 2 * t := self_le_two_mul t
    _ ≤ s + 2 * t := by simp
    _ = n := hn.symm

theorem codeUnpairGraph_snd_le
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {a b n : V}
    (h :
      Semiformula.Evalb (M := V)
        ![a, b, n] codeUnpairGraph.val) :
    b ≤ n :=
  codePairGraph_right_le ((codeUnpairGraph_iff_codePairGraph a b n).mp h)

theorem codeUnpairSndGraph_le
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {b n : V}
    (h :
      Semiformula.Evalb (M := V)
        ![b, n] codeUnpairSndGraph.val) :
    b ≤ n := by
  obtain ⟨a, ha⟩ := (codeUnpairSndGraph_iff b n).mp h
  exact codeUnpairGraph_snd_le ha

theorem codeUnpairSndGraph_lt_succ
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {b n : V}
    (h :
      Semiformula.Evalb (M := V)
        ![b, n] codeUnpairSndGraph.val) :
    b < n + 1 :=
  lt_of_le_of_lt (codeUnpairSndGraph_le h) (by simp)


/-! ### Fixed-input functionality of the pair graph

Proved directly from `isSpread_existsUnique` and `codePairGraph_iff`. This is the
functional direction -- fixed inputs determine the output -- and is not obtained
from `codePairGraph_injective`, which fixes the output and constrains the
inputs. -/

theorem codePairGraph_existsUnique
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (x tail : V) :
    ∃! m : V,
      Semiformula.Evalb (M := V)
        ![m, x, tail] codePairGraph.val := by
  obtain ⟨s, hs, hsu⟩ := isSpread_existsUnique (V := V) x
  obtain ⟨t, ht, htu⟩ := isSpread_existsUnique (V := V) tail
  refine ⟨s + 2 * t, (codePairGraph_iff _ x tail).mpr ⟨s, t, hs, ht, rfl⟩, ?_⟩
  intro m hm
  obtain ⟨s', t', hs', ht', hmeq⟩ := (codePairGraph_iff m x tail).mp hm
  rw [hmeq, hsu s' hs', htu t' ht']

/-! ### The fixed one-step formula

Output-first: `#0` is the constructed list code, `#1` the decoded head, `#2` the
encoded tail. That order is what a later cons-step graph for internal vector
recursion needs; the decoder order `head, tail, code` is a different interface
and is not used here. -/

noncomputable def listConsGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “c x tail. ∃ m, c = m + 1 ∧ !codeUnpairGraph x tail m”

theorem listConsGraph_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c x tail : V) :
    Semiformula.Evalb (M := V)
      ![c, x, tail] listConsGraph.val ↔
    ∃ m : V,
      c = m + 1 ∧
      Semiformula.Evalb (M := V)
        ![x, tail, m] codeUnpairGraph.val := by
  simp [listConsGraph]

theorem listConsGraph_iff_codePairGraph
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c x tail : V) :
    Semiformula.Evalb (M := V)
      ![c, x, tail] listConsGraph.val ↔
    ∃ m : V,
      c = m + 1 ∧
      Semiformula.Evalb (M := V)
        ![m, x, tail] codePairGraph.val := by
  rw [listConsGraph_iff]
  constructor
  · rintro ⟨m, hc, hm⟩
    exact ⟨m, hc, (codeUnpairGraph_iff_codePairGraph x tail m).mp hm⟩
  · rintro ⟨m, hc, hm⟩
    exact ⟨m, hc, (codeUnpairGraph_iff_codePairGraph x tail m).mpr hm⟩

/-- The successor specialization. The general bridge supplies `m + 1 = m' + 1`;
the two predecessors are identified by the pinned generic `succ_inj`. -/
theorem listConsGraph_succ_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (m x tail : V) :
    Semiformula.Evalb (M := V)
      ![m + 1, x, tail] listConsGraph.val ↔
    Semiformula.Evalb (M := V)
      ![x, tail, m] codeUnpairGraph.val := by
  rw [listConsGraph_iff]
  constructor
  · rintro ⟨m', hc, hm'⟩
    have hmm : m = m' := succ_inj hc
    rw [hmm]
    exact hm'
  · intro h
    exact ⟨m, rfl, h⟩

/-- Zero is never a cons code, by the pinned zero/successor disjointness
`Arithmetic.succ_ne_zero`. -/
theorem listConsGraph_zero_false
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (x tail : V) :
    ¬Semiformula.Evalb (M := V)
      ![(0 : V), x, tail] listConsGraph.val := by
  intro h
  obtain ⟨m, hc, -⟩ := (listConsGraph_iff 0 x tail).mp h
  exact Arithmetic.succ_ne_zero m hc.symm

theorem listConsGraph_existsUnique_code
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (x tail : V) :
    ∃! c : V,
      Semiformula.Evalb (M := V)
        ![c, x, tail] listConsGraph.val := by
  obtain ⟨m, hm, hmu⟩ := codePairGraph_existsUnique x tail
  refine ⟨m + 1, (listConsGraph_iff_codePairGraph _ x tail).mpr ⟨m, rfl, hm⟩, ?_⟩
  intro c hc
  obtain ⟨m', hceq, hm'⟩ := (listConsGraph_iff_codePairGraph c x tail).mp hc
  rw [hceq, hmu m' hm']

theorem listConsGraph_existsUnique_pair_of_ne_zero
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c : V)
    (hc : c ≠ 0) :
    ∃! p : V × V,
      Semiformula.Evalb (M := V)
        ![c, p.1, p.2] listConsGraph.val := by
  obtain ⟨m, rfl⟩ := exists_succ_of_ne_zero hc
  obtain ⟨p, hp, hpu⟩ := codeUnpairGraph_existsUnique (V := V) m
  refine ⟨p, (listConsGraph_succ_iff m p.1 p.2).mpr hp, ?_⟩
  intro q hq
  exact hpu q ((listConsGraph_succ_iff m q.1 q.2).mp hq)

/-- Strict descent, from the all-model bound `codeUnpairGraph_snd_le`. Not from
standard-model termination and not from the project's `codeUnpair_right_le`. -/
theorem listConsGraph_tail_lt
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {c x tail : V}
    (h :
      Semiformula.Evalb (M := V)
        ![c, x, tail] listConsGraph.val) :
    tail < c := by
  obtain ⟨m, hceq, hm⟩ := (listConsGraph_iff c x tail).mp h
  have hle : tail ≤ m := codeUnpairGraph_snd_le hm
  rw [hceq]
  exact lt_of_le_of_lt hle (by simp)

theorem listConsGraph_zero_or_existsUnique_pair
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c : V) :
    c = 0 ∨
    ∃! p : V × V,
      Semiformula.Evalb (M := V)
        ![c, p.1, p.2] listConsGraph.val := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact Or.inl rfl
  · exact Or.inr (listConsGraph_existsUnique_pair_of_ne_zero c hc)

/-! ### Standard-model constructor and decoder equations -/

theorem listConsGraph_nat_iff
    (c x tail : ℕ) :
    Semiformula.Evalb (M := ℕ)
      ![c, x, tail] listConsGraph.val ↔
    c = Metamath.Feferman.codePair x tail + 1 := by
  rw [listConsGraph_iff_codePairGraph]
  constructor
  · rintro ⟨m, hc, hm⟩
    rw [hc, (codePairGraph_nat_iff m x tail).mp hm]
  · intro h
    exact ⟨Metamath.Feferman.codePair x tail, h,
      (codePairGraph_nat_iff _ x tail).mpr rfl⟩

theorem listConsGraph_nat_succ_iff
    (m x tail : ℕ) :
    Semiformula.Evalb (M := ℕ)
      ![m + 1, x, tail] listConsGraph.val ↔
    (x, tail) = Metamath.Feferman.codeUnpair m := by
  rw [listConsGraph_succ_iff]
  exact codeUnpairGraph_nat_iff x tail m


/-! ### The semantic constructor

`listConsGraph` was fixed independently in the copied base, and
`listConsGraph_existsUnique_code` proved arbitrary-model existence and
uniqueness of its output for every pair of inputs. The value below merely
realizes that prior graph; the graph is not redefined from it, and no
standard-model fact justifies the selection. -/

noncomputable def listConsValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (x tail : V) : V :=
  Classical.choose!
    (listConsGraph_existsUnique_code (V := V) x tail)

theorem listConsValue_spec
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (x tail : V) :
    Semiformula.Evalb (M := V)
      ![listConsValue x tail, x, tail] listConsGraph.val :=
  Classical.choose!_spec (listConsGraph_existsUnique_code (V := V) x tail)

theorem listConsGraph_iff_listConsValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c x tail : V) :
    Semiformula.Evalb (M := V)
      ![c, x, tail] listConsGraph.val ↔
    c = listConsValue x tail := by
  constructor
  · -- uniqueness applied with the candidate `c` first, so the orientation is
    -- already `c = listConsValue x tail`
    intro h
    exact Classical.choose_uniq (listConsGraph_existsUnique_code (V := V) x tail) h
  · rintro rfl
    exact listConsValue_spec x tail

/-! ### The defining-function certificate

`DefinedFunction` is output-first: variable `0` is the value of the function at
variables `1` and `2`, which is exactly the order `listConsGraph` was fixed
with. -/

theorem listConsValue_defined
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    𝚺₁-Function₂[V]
      (listConsValue (V := V)) via listConsGraph :=
  .mk fun v ↦ by
    change Semiformula.Evalb (M := V) v listConsGraph.val ↔
      v 0 = listConsValue (v 1) (v 2)
    rw [show v = ![v 0, v 1, v 2] from Matrix.fun_eq_vec_three v]
    exact listConsGraph_iff_listConsValue (V := V) (v 0) (v 1) (v 2)

instance listConsValue_definable
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    𝚺₁-Function₂[V]
      (listConsValue (V := V)) :=
  listConsValue_defined.to_definable

/-! ### Standard-model value and descent -/

theorem listConsValue_nat
    (x tail : ℕ) :
    listConsValue x tail =
      Metamath.Feferman.codePair x tail + 1 :=
  (listConsGraph_nat_iff _ x tail).mp (listConsValue_spec x tail)

theorem listConsValue_tail_lt
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (x tail : V) :
    tail < listConsValue x tail :=
  listConsGraph_tail_lt (listConsValue_spec x tail)


/-! ### The recursive-step formula -/

noncomputable def listEncodeStep : 𝚺₁.Semisentence 4 := .mkSigma
  “y x xs ih. !listConsGraph y x ih”

theorem listEncodeStep_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y x xs ih : V) :
    Semiformula.Evalb (M := V)
      ![y, x, xs, ih] listEncodeStep.val ↔
    Semiformula.Evalb (M := V)
      ![y, x, ih] listConsGraph.val := by
  simp [listEncodeStep]

/-- Wiring check: the step result depends on the recursive result `ih` and is
independent of the Foundation structural tail `xs`. -/
theorem listEncodeStep_iff_listConsValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y x xs ih : V) :
    Semiformula.Evalb (M := V)
      ![y, x, xs, ih] listEncodeStep.val ↔
    y = listConsValue x ih := by
  rw [listEncodeStep_iff]
  exact listConsGraph_iff_listConsValue y x ih

/-! ### Blueprint and construction -/

noncomputable def listEncodeBlueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. y = 0”
  adjoin := listEncodeStep

noncomputable def listEncodeConstruction
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    VecRec.Construction V listEncodeBlueprint where
  nil _ := 0
  adjoin _ x _xs ih := listConsValue x ih
  nil_defined := .mk fun v ↦ by simp [listEncodeBlueprint]
  adjoin_defined := .mk fun v ↦ by
    change Semiformula.Evalb (M := V) v listEncodeStep.val ↔
      v 0 = listConsValue (v 1) (v 3)
    rw [show v = ![v 0, v 1, v 2, v 3] from Matrix.fun_eq_vec_four v]
    exact listEncodeStep_iff_listConsValue (V := V) (v 0) (v 1) (v 2) (v 3)

/-! ### The fold value and its recurrences -/

noncomputable def listEncodeValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (xs : V) : V :=
  (listEncodeConstruction (V := V)).result ![] xs

@[simp] theorem listEncodeValue_nil
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    listEncodeValue (V := V) 0 = 0 := by
  simp [listEncodeValue, listEncodeConstruction]

@[simp] theorem listEncodeValue_adjoin
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (x xs : V) :
    listEncodeValue (x ∷ xs) =
      listConsValue x (listEncodeValue xs) := by
  simp [listEncodeValue, listEncodeConstruction]

theorem listEncodeValue_adjoin_spec
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (x xs : V) :
    Semiformula.Evalb (M := V)
      ![listEncodeValue (x ∷ xs), x, listEncodeValue xs]
      listConsGraph.val := by
  rw [listEncodeValue_adjoin]
  exact listConsValue_spec x (listEncodeValue xs)

/-! ### The result graph and its definability -/

noncomputable def listEncodeGraph : 𝚺₁.Semisentence 2 :=
  listEncodeBlueprint.resultDef

theorem listEncodeValue_defined
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    𝚺₁-Function₁[V]
      (listEncodeValue (V := V)) via listEncodeGraph :=
  (listEncodeConstruction (V := V)).result_defined

instance listEncodeValue_definable
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    𝚺₁-Function₁[V] (listEncodeValue (V := V)) :=
  listEncodeValue_defined.to_definable

theorem listEncodeGraph_iff_listEncodeValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y xs : V) :
    Semiformula.Evalb (M := V)
      ![y, xs] listEncodeGraph.val ↔
    y = listEncodeValue xs :=
  (listEncodeConstruction (V := V)).eval_resultDef ![y, xs]

theorem listEncodeGraph_existsUnique
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (xs : V) :
    ∃! y : V,
      Semiformula.Evalb (M := V)
        ![y, xs] listEncodeGraph.val := by
  refine ⟨listEncodeValue xs,
    (listEncodeGraph_iff_listEncodeValue _ xs).mpr rfl, ?_⟩
  intro y hy
  exact (listEncodeGraph_iff_listEncodeValue y xs).mp hy

theorem listEncodeGraph_nil_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y : V) :
    Semiformula.Evalb (M := V)
      ![y, 0] listEncodeGraph.val ↔
    y = 0 := by
  rw [listEncodeGraph_iff_listEncodeValue, listEncodeValue_nil]

theorem listEncodeGraph_adjoin_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y x xs : V) :
    Semiformula.Evalb (M := V)
      ![y, x ∷ xs] listEncodeGraph.val ↔
    Semiformula.Evalb (M := V)
      ![y, x, listEncodeValue xs] listConsGraph.val := by
  rw [listEncodeGraph_iff_listEncodeValue, listEncodeValue_adjoin,
    listConsGraph_iff_listConsValue]

/-- The graph-only recurrence, derived from the unique forward fold. No second
encoder is introduced and no tail code is chosen independently. -/
theorem listEncodeGraph_adjoin_rel_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y x xs : V) :
    Semiformula.Evalb (M := V)
      ![y, x ∷ xs] listEncodeGraph.val ↔
    ∃ tailCode : V,
      Semiformula.Evalb (M := V)
        ![tailCode, xs] listEncodeGraph.val ∧
      Semiformula.Evalb (M := V)
        ![y, x, tailCode] listConsGraph.val := by
  constructor
  · intro h
    refine ⟨listEncodeValue xs,
      (listEncodeGraph_iff_listEncodeValue _ xs).mpr rfl, ?_⟩
    exact (listEncodeGraph_adjoin_iff y x xs).mp h
  · rintro ⟨tailCode, htail, hcons⟩
    have ht : tailCode = listEncodeValue xs :=
      (listEncodeGraph_iff_listEncodeValue tailCode xs).mp htail
    rw [ht] at hcons
    exact (listEncodeGraph_adjoin_iff y x xs).mpr hcons

/-! ### Standard-model agreement

`natVecOfList` is a standard-model comparison map only. It does not represent
every internal Vec of a nonstandard model, and it takes no part in any
arbitrary-model construction or definability proof above. -/

noncomputable def natVecOfList : List ℕ → ℕ
  | [] => 0
  | x :: xs => x ∷ natVecOfList xs

@[simp] theorem natVecOfList_nil :
    natVecOfList [] = 0 := rfl

@[simp] theorem natVecOfList_cons
    (x : ℕ) (xs : List ℕ) :
    natVecOfList (x :: xs) = x ∷ natVecOfList xs := rfl

theorem listEncodeValue_natVecOfList
    (xs : List ℕ) :
    listEncodeValue (natVecOfList xs) =
      Metamath.Feferman.listEncode xs := by
  induction xs with
  | nil => simp [Metamath.Feferman.listEncode]
  | cons x xs ih =>
    rw [natVecOfList_cons, listEncodeValue_adjoin, ih, listConsValue_nat,
      Metamath.Feferman.listEncode]

theorem listEncodeGraph_nat_iff
    (y : ℕ) (xs : List ℕ) :
    Semiformula.Evalb (M := ℕ)
      ![y, natVecOfList xs] listEncodeGraph.val ↔
    y = Metamath.Feferman.listEncode xs := by
  rw [listEncodeGraph_iff_listEncodeValue, listEncodeValue_natVecOfList]


/-! ### The range predicate

`xs : V` below is a single internal Foundation Vec code, not an external Lean
list. The fixed `listEncodeGraph` formula is the atomic semantic boundary: the
`VecRec` construction underneath it is never unfolded here. -/

def ListEncodable
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y : V) : Prop :=
  ∃ xs : V,
    Semiformula.Evalb (M := V)
      ![y, xs] listEncodeGraph.val

noncomputable def listEncodableDef : 𝚺₁.Semisentence 1 := .mkSigma
  “y. ∃ xs, !listEncodeGraph y xs”

theorem listEncodableDef_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y : V) :
    Semiformula.Evalb (M := V)
      ![y] listEncodableDef.val ↔
    ListEncodable y := by
  simp [listEncodableDef, ListEncodable]

theorem listEncodable_defined
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    𝚺₁-Predicate
      (ListEncodable (V := V)) via listEncodableDef :=
  .mk fun v ↦ by
    change Semiformula.Evalb (M := V) v listEncodableDef.val ↔ ListEncodable (v 0)
    rw [show v = ![v 0] from Matrix.fun_eq_vec_one v]
    exact listEncodableDef_iff (V := V) (v 0)

instance listEncodable_definable
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    𝚺₁-Predicate (ListEncodable (V := V)) :=
  listEncodable_defined.to_definable

/-! ### Internal strong-order induction

The recursive tail is known only to be strictly smaller than the full code, so
the induction is `ISigma1.sigma1_order_induction`. Three objects are kept
distinct: the project tail *code* `tail`, the internal Vec `xs` supplied by the
induction hypothesis at `tail`, and the new internal Vec `x ∷ xs`. The induction
hypothesis is applied to the project code `tail`, never to a Foundation
structural tail, and the constructed Vec is `x ∷ xs`, never `x ∷ tail`. -/

theorem listEncodable_all
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y : V) :
    ListEncodable y := by
  induction y using ISigma1.sigma1_order_induction with
  | hP => exact listEncodable_definable
  | ind y ih =>
    rcases listConsGraph_zero_or_existsUnique_pair (V := V) y with hy | hpair
    · subst hy
      exact ⟨0, (listEncodeGraph_nil_iff (V := V) 0).mpr rfl⟩
    · -- the uniqueness component of the one-step decomposition is not used, and
      -- is not uniqueness of the complete internal Vec preimage
      obtain ⟨p, hp, _hpu⟩ := hpair
      rcases p with ⟨x, tail⟩
      have htail : tail < y := listConsGraph_tail_lt hp
      obtain ⟨xs, hxs⟩ := ih tail htail
      exact ⟨x ∷ xs,
        (listEncodeGraph_adjoin_rel_iff (V := V) y x xs).mpr ⟨tail, hxs, hp⟩⟩

/-! ### Surjectivity -/

theorem listEncodeGraph_surjective
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y : V) :
    ∃ xs : V,
      Semiformula.Evalb (M := V)
        ![y, xs] listEncodeGraph.val :=
  listEncodable_all y

theorem listEncodeValue_surjective
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    Function.Surjective
      (listEncodeValue (V := V)) := by
  intro y
  obtain ⟨xs, hxs⟩ := listEncodeGraph_surjective (V := V) y
  -- the graph gives `y = listEncodeValue xs`; surjectivity wants the symmetric form
  exact ⟨xs, ((listEncodeGraph_iff_listEncodeValue y xs).mp hxs).symm⟩


/-! ### One-step input injectivity

Input-pair injectivity at a *fixed output*. This is not
`listConsGraph_existsUnique_code`, which is output functionality at fixed
inputs; the two run in opposite functional directions. No new choice is
needed. -/

theorem listConsGraph_injective_inputs
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {c x tail x' tail' : V}
    (h :
      Semiformula.Evalb (M := V)
        ![c, x, tail] listConsGraph.val)
    (h' :
      Semiformula.Evalb (M := V)
        ![c, x', tail'] listConsGraph.val) :
    x = x' ∧ tail = tail' := by
  have hc : c ≠ 0 := by
    rintro rfl
    exact listConsGraph_zero_false x tail h
  obtain ⟨p, _hp, hpu⟩ := listConsGraph_existsUnique_pair_of_ne_zero (V := V) c hc
  have e1 : ((x, tail) : V × V) = p := hpu (x, tail) h
  have e2 : ((x', tail') : V × V) = p := hpu (x', tail') h'
  have e : ((x, tail) : V × V) = (x', tail') := e1.trans e2.symm
  exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩

/-! ### Zero output characterizes the internal nil Vec

Distinct from `listEncodeGraph_nil_iff`:

    listEncodeGraph_nil_iff y  : Graph y 0 ↔ y = 0
    listEncodeGraph_zero_iff xs : Graph 0 xs ↔ xs = 0

The adjoin case is discharged by `listConsGraph_zero_false`, not by an invented
inconsistency. -/

theorem listEncodeGraph_zero_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (xs : V) :
    Semiformula.Evalb (M := V)
      ![(0 : V), xs] listEncodeGraph.val ↔
    xs = 0 := by
  constructor
  · intro h
    rcases nil_or_adjoin xs with rfl | ⟨x, v, rfl⟩
    · rfl
    · exact absurd ((listEncodeGraph_adjoin_iff (0 : V) x v).mp h)
        (listConsGraph_zero_false x (listEncodeValue v))
  · rintro rfl
    exact (listEncodeGraph_nil_iff (V := V) 0).mpr rfl

/-! ### The Π₁ induction predicate

The graph atoms are `𝚺₁` but occur negatively, as implication antecedents, so
the complete predicate is `𝚷₁`. The certificate below is explicit; no stronger
hierarchy assumption is used and the `VecRec` construction is never unfolded
during the definability step. -/

def EncodeInjectiveAt
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (xs : V) : Prop :=
  ∀ ys y : V,
    Semiformula.Evalb (M := V)
      ![y, xs] listEncodeGraph.val →
    Semiformula.Evalb (M := V)
      ![y, ys] listEncodeGraph.val →
    xs = ys

noncomputable def encodeInjectiveAtDef :
    𝚷₁.Semisentence 1 := .mkPi
  “xs. ∀ ys, ∀ y,
    !listEncodeGraph y xs →
    !listEncodeGraph y ys →
    xs = ys”

theorem encodeInjectiveAtDef_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (xs : V) :
    Semiformula.Evalb (M := V)
      ![xs] encodeInjectiveAtDef.val ↔
    EncodeInjectiveAt xs := by
  simp [encodeInjectiveAtDef, EncodeInjectiveAt]

theorem encodeInjectiveAt_defined
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    𝚷₁-Predicate
      (EncodeInjectiveAt (V := V))
      via encodeInjectiveAtDef :=
  .mk fun v ↦ by
    change Semiformula.Evalb (M := V) v encodeInjectiveAtDef.val ↔
      EncodeInjectiveAt (v 0)
    rw [show v = ![v 0] from Matrix.fun_eq_vec_one v]
    exact encodeInjectiveAtDef_iff (V := V) (v 0)

instance encodeInjectiveAt_definable
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    𝚷₁-Predicate
      (EncodeInjectiveAt (V := V)) :=
  encodeInjectiveAt_defined.to_definable

/-! ### Internal structural induction

Four objects are kept apart: the Foundation structural Vec tails `xs` and `xs'`,
their project tail codes `listEncodeValue xs` and `listEncodeValue xs'`, the
equality of project tail codes delivered by one-step input injectivity, and the
equality `xs = xs'` delivered by the induction hypothesis. The hypothesis is
applied to the structural tail `xs`, never to a project tail code, and
`x ∷ xs` is never identified with `listConsValue x (listEncodeValue xs)`. -/

theorem encodeInjectiveAt_all
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (xs : V) :
    EncodeInjectiveAt xs := by
  induction xs using adjoin_ISigma1.pi1_succ_induction with
  | hP => exact encodeInjectiveAt_definable
  | nil =>
    intro ys y h0 hys
    have hy : y = 0 := (listEncodeGraph_nil_iff y).mp h0
    subst hy
    exact ((listEncodeGraph_zero_iff ys).mp hys).symm
  | adjoin x xs ih =>
    intro ys y h hys
    rcases nil_or_adjoin ys with rfl | ⟨x', xs', rfl⟩
    · have hy : y = 0 := (listEncodeGraph_nil_iff y).mp hys
      subst hy
      exact (listEncodeGraph_zero_iff (x ∷ xs)).mp h
    · have h1 := (listEncodeGraph_adjoin_iff y x xs).mp h
      have h2 := (listEncodeGraph_adjoin_iff y x' xs').mp hys
      obtain ⟨hx, htail⟩ := listConsGraph_injective_inputs h1 h2
      have hxs : xs = xs' :=
        ih xs' (listEncodeValue xs)
          ((listEncodeGraph_iff_listEncodeValue _ xs).mpr rfl)
          ((listEncodeGraph_iff_listEncodeValue _ xs').mpr htail)
      rw [hx, hxs]

/-! ### Public injectivity -/

theorem listEncodeGraph_injective
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {y xs ys : V}
    (hxs :
      Semiformula.Evalb (M := V)
        ![y, xs] listEncodeGraph.val)
    (hys :
      Semiformula.Evalb (M := V)
        ![y, ys] listEncodeGraph.val) :
    xs = ys :=
  encodeInjectiveAt_all xs ys y hxs hys

theorem listEncodeValue_injective
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    Function.Injective
      (listEncodeValue (V := V)) := by
  intro xs ys h
  refine listEncodeGraph_injective (y := listEncodeValue xs) ?_ ?_
  · exact (listEncodeGraph_iff_listEncodeValue _ xs).mpr rfl
  · exact (listEncodeGraph_iff_listEncodeValue _ ys).mpr h


/-! ### Unique encoder preimages

Existence from surjectivity, uniqueness from injectivity. No function is
selected at this stage. -/

theorem listEncodeGraph_existsUnique_preimage
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y : V) :
    ∃! xs : V,
      Semiformula.Evalb (M := V)
        ![y, xs] listEncodeGraph.val := by
  obtain ⟨xs, hxs⟩ := listEncodeGraph_surjective (V := V) y
  refine ⟨xs, hxs, ?_⟩
  intro xs' hxs'
  -- competing candidate first, displayed witness second
  exact listEncodeGraph_injective hxs' hxs

theorem listEncodeValue_bijective
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    Function.Bijective
      (listEncodeValue (V := V)) :=
  ⟨listEncodeValue_injective,
    listEncodeValue_surjective⟩

/-! ### The fixed converse graph

`#0` is the decoded internal Foundation Vec, `#1` the encoded project list code.
The formula is fixed independently; it is not defined from any selected
decoder. -/

noncomputable def listDecodeGraph :
    𝚺₁.Semisentence 2 := .mkSigma
  “xs y. !listEncodeGraph y xs”

theorem listDecodeGraph_iff_listEncodeGraph
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (xs y : V) :
    Semiformula.Evalb (M := V)
      ![xs, y] listDecodeGraph.val ↔
    Semiformula.Evalb (M := V)
      ![y, xs] listEncodeGraph.val := by
  -- Keep `eval_substs` out of the simplifier: descending through the resulting
  -- evaluation of `listEncodeGraph` exhausts memory on the pinned Lean.
  simp only [listDecodeGraph, HierarchySymbol.Semiformula.val_mkSigma]
  rw [Semiformula.eval_substs]
  exact Iff.of_eq (congrArg
    (fun e ↦ Semiformula.Evalb (M := V) e listEncodeGraph.val)
    (by
      apply Fin.funext_two
      · rfl
      · rfl
      · intro i
        exact Fin.elim0 i))

theorem listDecodeGraph_existsUnique
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y : V) :
    ∃! xs : V,
      Semiformula.Evalb (M := V)
        ![xs, y] listDecodeGraph.val := by
  obtain ⟨xs, hxs, hu⟩ := listEncodeGraph_existsUnique_preimage (V := V) y
  refine ⟨xs, (listDecodeGraph_iff_listEncodeGraph xs y).mpr hxs, ?_⟩
  intro xs' hxs'
  exact hu xs' ((listDecodeGraph_iff_listEncodeGraph xs' y).mp hxs')

/-! ### The selector, introduced only after all-model unique existence -/

noncomputable def listDecodeValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y : V) : V :=
  Classical.choose!
    (listDecodeGraph_existsUnique (V := V) y)

theorem listDecodeValue_spec
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y : V) :
    Semiformula.Evalb (M := V)
      ![listDecodeValue y, y] listDecodeGraph.val :=
  Classical.choose!_spec (listDecodeGraph_existsUnique (V := V) y)

theorem listDecodeValue_encode_spec
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y : V) :
    Semiformula.Evalb (M := V)
      ![y, listDecodeValue y] listEncodeGraph.val :=
  (listDecodeGraph_iff_listEncodeGraph (listDecodeValue y) y).mp
    (listDecodeValue_spec y)

/-! ### Graph and value bridges -/

theorem listDecodeGraph_iff_listDecodeValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (xs y : V) :
    Semiformula.Evalb (M := V)
      ![xs, y] listDecodeGraph.val ↔
    xs = listDecodeValue y := by
  constructor
  · intro h
    exact Classical.choose_uniq (listDecodeGraph_existsUnique (V := V) y) h
  · rintro rfl
    exact listDecodeValue_spec y

theorem listEncodeGraph_iff_listDecodeValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y xs : V) :
    Semiformula.Evalb (M := V)
      ![y, xs] listEncodeGraph.val ↔
    xs = listDecodeValue y :=
  (listDecodeGraph_iff_listEncodeGraph xs y).symm.trans
    (listDecodeGraph_iff_listDecodeValue xs y)

/-! ### Definability of the selected decoder -/

theorem listDecodeValue_defined
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    𝚺₁-Function₁[V]
      (listDecodeValue (V := V))
      via listDecodeGraph :=
  .mk fun v ↦ by
    change Semiformula.Evalb (M := V) v listDecodeGraph.val ↔
      v 0 = listDecodeValue (v 1)
    rw [show v = ![v 0, v 1] from Matrix.fun_eq_vec_two v]
    exact listDecodeGraph_iff_listDecodeValue (V := V) (v 0) (v 1)

instance listDecodeValue_definable
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    𝚺₁-Function₁[V]
      (listDecodeValue (V := V)) :=
  listDecodeValue_defined.to_definable

/-! ### All-model inverse laws

Neither project standard-model inverse theorem is used here. -/

theorem listDecodeValue_leftInverse
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    Function.LeftInverse
      (listDecodeValue (V := V))
      (listEncodeValue (V := V)) := by
  intro xs
  -- selected preimage first, canonical preimage second
  exact listEncodeGraph_injective
    (listDecodeValue_encode_spec (listEncodeValue xs))
    ((listEncodeGraph_iff_listEncodeValue _ xs).mpr rfl)

theorem listDecodeValue_rightInverse
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    Function.RightInverse
      (listDecodeValue (V := V))
      (listEncodeValue (V := V)) := by
  intro y
  -- the graph gives `y = listEncodeValue (listDecodeValue y)`; reverse once
  exact ((listEncodeGraph_iff_listEncodeValue y (listDecodeValue y)).mp
    (listDecodeValue_encode_spec y)).symm

/-! ### Standard-model agreement

`natVecOfList` is a standard-model comparison map only. Nothing below claims
that every internal Vec of a nonstandard model is its image. -/

theorem listDecodeValue_nat
    (n : ℕ) :
    listDecodeValue n =
      natVecOfList
        (Metamath.Feferman.listDecode n) :=
  listEncodeGraph_injective
    (listDecodeValue_encode_spec n)
    ((listEncodeGraph_nat_iff
        n (Metamath.Feferman.listDecode n)).mpr
      (Metamath.Feferman.listEncode_listDecode n).symm)

theorem listDecodeGraph_nat_iff
    (xs n : ℕ) :
    Semiformula.Evalb (M := ℕ)
      ![xs, n] listDecodeGraph.val ↔
    xs =
      natVecOfList
        (Metamath.Feferman.listDecode n) := by
  rw [listDecodeGraph_iff_listDecodeValue, listDecodeValue_nat]


/-! ### Binary append on internal Foundation Vecs

Foundation's `concat` is not binary append: its nil case is `?[param 0]`, so it
appends a single element. It is not used anywhere below. The construction here
takes the right-hand Vec as the fixed parameter and returns it unchanged in the
nil case. -/

noncomputable def vecAppendBlueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y ys. y = ys”
  adjoin := .mkSigma “y x xs ih ys. !adjoinDef y x ih”

noncomputable def vecAppendConstruction
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    VecRec.Construction V vecAppendBlueprint where
  nil param := param 0
  adjoin _ x _xs ih := x ∷ ih
  nil_defined := .mk fun v ↦ by
    simp [vecAppendBlueprint]
  adjoin_defined := .mk fun v ↦ by
    simp [vecAppendBlueprint, Fin.isValue]

noncomputable def vecAppendValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (xs ys : V) : V :=
  (vecAppendConstruction (V := V)).result ![ys] xs

@[simp] theorem vecAppendValue_nil
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (ys : V) :
    vecAppendValue 0 ys = ys := by
  simp [vecAppendValue, vecAppendConstruction]

@[simp] theorem vecAppendValue_adjoin
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (x xs ys : V) :
    vecAppendValue (x ∷ xs) ys =
      x ∷ vecAppendValue xs ys := by
  simp [vecAppendValue, vecAppendConstruction]

/-! ### The fixed append graph

`#0` output, `#1` left internal Vec, `#2` right internal Vec. -/

noncomputable def vecAppendGraph : 𝚺₁.Semisentence 3 :=
  vecAppendBlueprint.resultDef

theorem vecAppendValue_defined
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    𝚺₁-Function₂[V]
      (vecAppendValue (V := V)) via vecAppendGraph :=
  (vecAppendConstruction (V := V)).result_defined

instance vecAppendValue_definable
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    𝚺₁-Function₂[V]
      (vecAppendValue (V := V)) :=
  vecAppendValue_defined.to_definable

theorem vecAppendGraph_iff_vecAppendValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y xs ys : V) :
    Semiformula.Evalb (M := V)
      ![y, xs, ys] vecAppendGraph.val ↔
    y = vecAppendValue xs ys := by
  change
    vecAppendBlueprint.resultDef.val.Evalb ![y, xs, ys] ↔
      y =
        (vecAppendConstruction (V := V)).result ![ys] xs
  exact
    (vecAppendConstruction (V := V)).eval_resultDef
      ![y, xs, ys]

theorem vecAppendGraph_existsUnique
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (xs ys : V) :
    ∃! y : V,
      Semiformula.Evalb (M := V)
        ![y, xs, ys] vecAppendGraph.val := by
  refine ⟨vecAppendValue xs ys,
    (vecAppendGraph_iff_vecAppendValue _ _ _).mpr rfl, ?_⟩
  intro y hy
  exact (vecAppendGraph_iff_vecAppendValue y xs ys).mp hy

theorem vecAppendGraph_nil_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y ys : V) :
    Semiformula.Evalb (M := V)
      ![y, 0, ys] vecAppendGraph.val ↔
    y = ys := by
  rw [vecAppendGraph_iff_vecAppendValue, vecAppendValue_nil]

theorem vecAppendGraph_adjoin_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y x xs ys : V) :
    Semiformula.Evalb (M := V)
      ![y, x ∷ xs, ys] vecAppendGraph.val ↔
    y = x ∷ vecAppendValue xs ys := by
  rw [vecAppendGraph_iff_vecAppendValue, vecAppendValue_adjoin]

/-! ### Standard-model comparison

`natVecOfList` is a standard-model comparison map only; nothing here claims that
every internal Vec of an arbitrary model lies in its image. External `List`
induction occurs only in the next two theorems, and only on `xs`. -/

theorem len_natVecOfList
    (xs : List ℕ) :
    len (natVecOfList xs) = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem vecAppendValue_natVecOfList
    (xs ys : List ℕ) :
    vecAppendValue
        (natVecOfList xs)
        (natVecOfList ys) =
      natVecOfList (xs ++ ys) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem vecAppendGraph_nat_iff
    (y : ℕ) (xs ys : List ℕ) :
    Semiformula.Evalb (M := ℕ)
      ![y, natVecOfList xs, natVecOfList ys]
      vecAppendGraph.val ↔
    y = natVecOfList (xs ++ ys) := by
  rw [vecAppendGraph_iff_vecAppendValue, vecAppendValue_natVecOfList]


/-! ### The internal implication string

`0 ∷ (len a ∷ vecAppendValue a b)`: the leading zero is a *token* adjoined to a
Vec, not the nil Vec. The length is `len a`, the antecedent's, and the append is
`vecAppendValue a b`, not reversed. -/

noncomputable def impStringValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a b : V) : V :=
  (0 : V) ∷ (len a ∷ vecAppendValue a b)

/-- The graph, built structurally from the fixed component formulas `lenDef`,
`vecAppendGraph` and `adjoinDef`, independently of `impStringValue`.

    #0 = output internal implication string
    #1 = antecedent internal Vec
    #2 = consequent internal Vec

with witnesses in the order `l = len a`, `ab = vecAppendValue a b`,
`lab = l ∷ ab`, `y = 0 ∷ lab`. -/
noncomputable def impStringGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y a b.
    ∃ l, !lenDef l a ∧
    ∃ ab, !vecAppendGraph ab a b ∧
    ∃ lab, !adjoinDef lab l ab ∧
      !adjoinDef y 0 lab”

theorem impStringGraph_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y a b : V) :
    Semiformula.Evalb (M := V)
        ![y, a, b] impStringGraph.val ↔
      ∃ l : V,
        Semiformula.Evalb (M := V)
          ![l, a] lenDef.val ∧
      ∃ ab : V,
        Semiformula.Evalb (M := V)
          ![ab, a, b] vecAppendGraph.val ∧
      ∃ lab : V,
        Semiformula.Evalb (M := V)
          ![lab, l, ab] adjoinDef.val ∧
        Semiformula.Evalb (M := V)
          ![y, (0 : V), lab] adjoinDef.val := by
  simp [impStringGraph]

theorem impStringGraph_iff_impStringValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y a b : V) :
    Semiformula.Evalb (M := V)
        ![y, a, b] impStringGraph.val ↔
      y = impStringValue a b := by
  rw [impStringGraph_iff]
  constructor
  · rintro ⟨l, hl, ab, hab, lab, hlab, hy⟩
    have hl' : l = len a := by simpa using hl
    have hab' : ab = vecAppendValue a b :=
      (vecAppendGraph_iff_vecAppendValue ab a b).mp hab
    have hlab' : lab = l ∷ ab := by simpa using hlab
    have hy' : y = (0 : V) ∷ lab := by simpa using hy
    rw [hy', hlab', hl', hab', impStringValue]
  · rintro rfl
    exact ⟨len a, by simp,
      vecAppendValue a b, (vecAppendGraph_iff_vecAppendValue _ a b).mpr rfl,
      len a ∷ vecAppendValue a b, by simp, by simp [impStringValue]⟩

theorem impStringValue_spec
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a b : V) :
    Semiformula.Evalb (M := V)
      ![impStringValue a b, a, b]
      impStringGraph.val := by
  exact
    (impStringGraph_iff_impStringValue
      (impStringValue a b) a b).mpr rfl

theorem impStringGraph_existsUnique
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a b : V) :
    ∃! y : V,
      Semiformula.Evalb (M := V)
        ![y, a, b] impStringGraph.val := by
  refine
    ⟨impStringValue a b,
      impStringValue_spec a b, ?_⟩
  intro y hy
  exact
    (impStringGraph_iff_impStringValue y a b).mp hy

theorem impStringValue_defined
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    𝚺₁-Function₂[V]
      (impStringValue (V := V)) via impStringGraph :=
  .mk fun v ↦ by
    change
      Semiformula.Evalb (M := V)
          v impStringGraph.val ↔
        v 0 = impStringValue (v 1) (v 2)
    rw [
      show v = ![v 0, v 1, v 2]
        from Matrix.fun_eq_vec_three v
    ]
    exact
      impStringGraph_iff_impStringValue
        (V := V) (v 0) (v 1) (v 2)

instance impStringValue_definable
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    𝚺₁-Function₂[V]
      (impStringValue (V := V)) :=
  impStringValue_defined.to_definable

/-! ### Standard-model agreement

`natVecOfList` is a standard-model comparison map only; nothing here claims that
every internal Vec is its image. No new induction is used. -/

theorem impStringValue_natVecOfList
    (a b : List ℕ) :
    impStringValue
        (natVecOfList a)
        (natVecOfList b) =
      natVecOfList
        (Metamath.Feferman.impString a b) := by
  rw [impStringValue, len_natVecOfList, vecAppendValue_natVecOfList,
    Metamath.Feferman.impString, Metamath.Feferman.impTag,
    natVecOfList_cons, natVecOfList_cons]

theorem impStringGraph_nat_iff
    (y : ℕ) (a b : List ℕ) :
    Semiformula.Evalb (M := ℕ)
        ![y, natVecOfList a, natVecOfList b]
        impStringGraph.val ↔
      y =
        natVecOfList
          (Metamath.Feferman.impString a b) := by
  rw [
    impStringGraph_iff_impStringValue,
    impStringValue_natVecOfList
  ]


/-! ### Numerical implication, all-model

`a` and `b` are arbitrary-model numerical formula codes. The value composes the
already-justified decoder, the internal implication string, and the encoder; no
further selector, decoder or construction is introduced. -/

noncomputable def impValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a b : V) : V :=
  listEncodeValue
    (impStringValue
      (listDecodeValue a)
      (listDecodeValue b))

/-- The graph, built structurally from the fixed component graphs, independently
of `impValue`.

    #0 = output numerical implication code
    #1 = antecedent numerical formula code
    #2 = consequent numerical formula code

Witnesses in order: `da = listDecodeValue a`, `db = listDecodeValue b`,
`ds = impStringValue da db`, `y = listEncodeValue ds`. The decoder atom is
output-first in the decoded Vec and the encoder atom is output-first in the
code, so the two run in opposite directions; neither is reversed. -/
noncomputable def impGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y a b.
    ∃ da, !listDecodeGraph da a ∧
    ∃ db, !listDecodeGraph db b ∧
    ∃ ds, !impStringGraph ds da db ∧
      !listEncodeGraph y ds”

theorem impGraph_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y a b : V) :
    Semiformula.Evalb (M := V)
        ![y, a, b] impGraph.val ↔
      ∃ da : V,
        Semiformula.Evalb (M := V)
          ![da, a] listDecodeGraph.val ∧
      ∃ db : V,
        Semiformula.Evalb (M := V)
          ![db, b] listDecodeGraph.val ∧
      ∃ ds : V,
        Semiformula.Evalb (M := V)
          ![ds, da, db] impStringGraph.val ∧
        Semiformula.Evalb (M := V)
          ![y, ds] listEncodeGraph.val := by
  simp [impGraph]

theorem impGraph_iff_impValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y a b : V) :
    Semiformula.Evalb (M := V)
        ![y, a, b] impGraph.val ↔
      y = impValue a b := by
  rw [impGraph_iff]
  constructor
  · rintro ⟨da, hda, db, hdb, ds, hds, hy⟩
    have hda' : da = listDecodeValue a :=
      (listDecodeGraph_iff_listDecodeValue da a).mp hda
    have hdb' : db = listDecodeValue b :=
      (listDecodeGraph_iff_listDecodeValue db b).mp hdb
    have hds' : ds = impStringValue da db :=
      (impStringGraph_iff_impStringValue ds da db).mp hds
    have hy' : y = listEncodeValue ds :=
      (listEncodeGraph_iff_listEncodeValue y ds).mp hy
    rw [hy', hds', hda', hdb', impValue]
  · rintro rfl
    refine
      ⟨listDecodeValue a, listDecodeValue_spec a,
       listDecodeValue b, listDecodeValue_spec b,
       impStringValue (listDecodeValue a) (listDecodeValue b),
       impStringValue_spec _ _, ?_⟩
    exact
      (listEncodeGraph_iff_listEncodeValue _ _).mpr rfl

theorem impValue_spec
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a b : V) :
    Semiformula.Evalb (M := V)
      ![impValue a b, a, b] impGraph.val := by
  exact
    (impGraph_iff_impValue
      (impValue a b) a b).mpr rfl

theorem impGraph_existsUnique
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a b : V) :
    ∃! y : V,
      Semiformula.Evalb (M := V)
        ![y, a, b] impGraph.val := by
  refine
    ⟨impValue a b,
      impValue_spec a b, ?_⟩
  intro y hy
  exact
    (impGraph_iff_impValue y a b).mp hy

theorem impValue_defined
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    𝚺₁-Function₂[V]
      (impValue (V := V)) via impGraph :=
  .mk fun v ↦ by
    change
      Semiformula.Evalb (M := V)
          v impGraph.val ↔
        v 0 = impValue (v 1) (v 2)
    rw [
      show v = ![v 0, v 1, v 2]
        from Matrix.fun_eq_vec_three v
    ]
    exact
      impGraph_iff_impValue
        (V := V) (v 0) (v 1) (v 2)

instance impValue_definable
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
 :
    𝚺₁-Function₂[V]
      (impValue (V := V)) :=
  impValue_defined.to_definable

/-! ### Standard-model agreement

The only place the project numerical functions occur. The `change` step is
definitional unfolding of `impValue`, `Metamath.Feferman.imp`,
`Metamath.Feferman.encodeFormula` and `Metamath.Feferman.decodeFormula`; no
inverse theorem, induction, or new choice is used. -/

theorem impValue_nat
    (a b : ℕ) :
    impValue a b =
      Metamath.Feferman.imp a b := by
  change
    listEncodeValue
        (impStringValue
          (listDecodeValue a)
          (listDecodeValue b)) =
      Metamath.Feferman.listEncode
        (Metamath.Feferman.impString
          (Metamath.Feferman.listDecode a)
          (Metamath.Feferman.listDecode b))
  rw [
    listDecodeValue_nat a,
    listDecodeValue_nat b,
    impStringValue_natVecOfList,
    listEncodeValue_natVecOfList
  ]

theorem impGraph_nat_iff
    (y a b : ℕ) :
    Semiformula.Evalb (M := ℕ)
        ![y, a, b] impGraph.val ↔
      y = Metamath.Feferman.imp a b := by
  rw [
    impGraph_iff_impValue,
    impValue_nat
  ]

theorem nth_natVecOfList
    (xs : List ℕ) (i : ℕ) :
    nth (natVecOfList xs) i =
      xs.getD i 0 := by
  induction xs generalizing i with
  | nil =>
      rw [natVecOfList_nil, nth_zero_idx, List.getD_nil]
  | cons x xs ih =>
      cases i with
      | zero =>
          rw [natVecOfList_cons, nth_adjoin_zero,
              List.getD_cons_zero]
      | succ i =>
          -- After `natVecOfList_cons` the goal is already
          --   nth (x ∷ natVecOfList xs) (i + 1) = (x :: xs).getD (i + 1) 0
          -- so the supplied `change` step was a no-op and is omitted.
          rw [natVecOfList_cons, nth_adjoin_succ,
              List.getD_cons_succ, ih i]

theorem nthDef_nat_iff
    (y : ℕ) (xs : List ℕ) (i : ℕ) :
    Semiformula.Evalb (M := ℕ)
        ![y, natVecOfList xs, i] nthDef.val ↔
      y = xs.getD i 0 := by
  simpa only [nth_natVecOfList] using
    (show
      Semiformula.Evalb (M := ℕ)
          ![y, natVecOfList xs, i] nthDef.val ↔
        y = nth (natVecOfList xs) i
      from by simp)

private def logicalAxiomCodePred
    (Th : PRTheoryPresentation) : ℕ → Prop :=
  fun a => Th.toTheory.syn.logicalAxiom.Holds (decodeFormula a)

/-- The theory-axiom branch as a predicate on numerical formula codes. -/
private def theoryAxiomCodePred
    (Th : PRTheoryPresentation) : ℕ → Prop :=
  fun a => Th.toTheory.ax.Holds (decodeFormula a)

/-! ### Computability certificates

`Metamath.Feferman.primrecPred_holds` is private to `ProofCode.lean`. The same
helper is reproduced here so that this file can use it. -/

/-- A `StringPredicate` with a primitive-recursive test has a
primitive-recursive `Holds`. Local copy of the inaccessible private helper in
`ProofCode.lean`. -/
private theorem primrecPred_holds
    {P : StringPredicate} (h : Primrec P.test) :
    PrimrecPred P.Holds :=
  Primrec.eq.comp h (Primrec.const true)

private theorem primrecPred_logicalAxiomCodePred
    (Th : PRTheoryPresentation) :
    PrimrecPred (logicalAxiomCodePred Th) := by
  have h : PrimrecPred
      fun a : ℕ => Th.toTheory.syn.logicalAxiom.Holds (decodeFormula a) :=
    (primrecPred_holds Th.logicalAxiom_prim).comp primrec_decodeFormula
  exact h

private theorem primrecPred_theoryAxiomCodePred
    (Th : PRTheoryPresentation) :
    PrimrecPred (theoryAxiomCodePred Th) := by
  have h : PrimrecPred
      fun a : ℕ => Th.toTheory.ax.Holds (decodeFormula a) :=
    (primrecPred_holds Th.ax_prim).comp primrec_decodeFormula
  exact h

private theorem computablePred_logicalAxiomCodePred
    (Th : PRTheoryPresentation) :
    ComputablePred (logicalAxiomCodePred Th) := by
  obtain ⟨inst, h⟩ := primrecPred_logicalAxiomCodePred Th
  exact ⟨inst, h.to_comp⟩

private theorem computablePred_theoryAxiomCodePred
    (Th : PRTheoryPresentation) :
    ComputablePred (theoryAxiomCodePred Th) := by
  obtain ⟨inst, h⟩ := primrecPred_theoryAxiomCodePred Th
  exact ⟨inst, h.to_comp⟩

/-- Recursive enumerability, which is what `codeOfREPred` assumes. -/
private theorem rePred_logicalAxiomCodePred
    (Th : PRTheoryPresentation) :
    REPred (logicalAxiomCodePred Th) :=
  (computablePred_logicalAxiomCodePred Th).to_re

/-- Recursive enumerability, which is what `codeOfREPred` assumes. -/
private theorem rePred_theoryAxiomCodePred
    (Th : PRTheoryPresentation) :
    REPred (theoryAxiomCodePred Th) :=
  (computablePred_theoryAxiomCodePred Th).to_re

/-! ### The two fixed unary leaves

`#0` is the numerical formula code `a`. The `.mkSigma` wrapper is what makes
these typed `𝚺₁.Semisentence 1` rather than bare formulas. -/

/-- The logical-axiom leaf: a fixed unary Sigma-one formula in the single
variable `#0 = a`, depending only on `Th`. -/
noncomputable def logicalAxiomLeaf
    (Th : PRTheoryPresentation) : 𝚺₁.Semisentence 1 :=
  .mkSigma (codeOfREPred (logicalAxiomCodePred Th))
    (by simp [codeOfREPred, codeOfPartrec'])

/-- The theory-axiom leaf: a fixed unary Sigma-one formula in the single
variable `#0 = a`, depending only on `Th`. -/
noncomputable def theoryAxiomLeaf
    (Th : PRTheoryPresentation) : 𝚺₁.Semisentence 1 :=
  .mkSigma (codeOfREPred (theoryAxiomCodePred Th))
    (by simp [codeOfREPred, codeOfPartrec'])

/-! ### Standard-natural-number adequacy

Evaluation in `ℕ` only. No arbitrary-model claim is made. -/

/-- Standard-natural-number adequacy of the logical-axiom leaf. -/
theorem logicalAxiomLeaf_nat_iff
    (Th : PRTheoryPresentation) (a : ℕ) :
    (Semiformula.Evalb ![a]) (logicalAxiomLeaf Th).val ↔
      Th.toTheory.syn.logicalAxiom.Holds (decodeFormula a) := by
  change (codeOfREPred (logicalAxiomCodePred Th)).Evalb ![a] ↔ _
  simpa only [logicalAxiomCodePred] using
    (codeOfREPred_spec (rePred_logicalAxiomCodePred Th) (x := a))

/-- Standard-natural-number adequacy of the theory-axiom leaf. -/
theorem theoryAxiomLeaf_nat_iff
    (Th : PRTheoryPresentation) (a : ℕ) :
    (Semiformula.Evalb ![a]) (theoryAxiomLeaf Th).val ↔
      Th.toTheory.ax.Holds (decodeFormula a) := by
  change (codeOfREPred (theoryAxiomCodePred Th)).Evalb ![a] ↔ _
  simpa only [theoryAxiomCodePred] using
    (codeOfREPred_spec (rePred_theoryAxiomCodePred Th) (x := a))

/-- The reduced line predicate transcribed onto a list of numerical formula
codes. The default at an out-of-range index is the numerical code `0`, whose
decoded string is the empty string. -/
def LineJustifiedCodeNF
    (Th : TheoryPresentation) (q : List ℕ) (i : ℕ) : Prop :=
  i < q.length ∧
    (Th.syn.logicalAxiom.Holds (decodeFormula (q.getD i 0)) ∨
     Th.ax.Holds (decodeFormula (q.getD i 0)) ∨
     ∃ j < i, ∃ k < i,
       q.getD k 0 = imp (q.getD j 0) (q.getD i 0))

/-! ### The reduced line checker

Binary, with `#0 = q` the internal HFS Vec of numerical formula codes and
`#1 = i` the current line index.

This formula checks only the reduced rule body. It deliberately omits the range
condition `i < length q`; the later `proofGraph` bounded universal supplies it.
Because `nthDef` is zero-default, `lineCheck` alone is satisfiable out of range,
which is exactly why `lineCheck_nat_iff` below states the range conjunct
explicitly.

Witness order is `ci`, then `j`, `k`, `cj`, `ck`. The current-line code `ci` is
obtained once, before the disjunction, and both axiom leaves are applied to that
same `ci`.

MP orientation, matching `LineJustifiedCodeNF` and Feferman's convention:
`k` is the earlier implication line, `j` the earlier antecedent line, and `i`
the current consequent line. Since `impGraph` has argument order
`output implication, antecedent, consequent`, the atom `!impGraph ck cj ci`
asserts `ck = imp cj ci`. -/

noncomputable def lineCheck
    (Th : PRTheoryPresentation) : 𝚺₁.Semisentence 2 :=
  let logAx : 𝚺₁.Semisentence 1 := logicalAxiomLeaf Th
  let thAx : 𝚺₁.Semisentence 1 := theoryAxiomLeaf Th
  .mkSigma
    “q i.
      ∃ ci, !nthDef ci q i ∧
        (!logAx ci ∨
         !thAx ci ∨
         ∃ j < i, ∃ k < i,
           ∃ cj, !nthDef cj q j ∧
           ∃ ck, !nthDef ck q k ∧
             !impGraph ck cj ci)”

/-! ### Arbitrary-model expansion

The two axiom leaves stay opaque: their evaluations appear as unanalysed
`Semiformula.Evalb` atoms on both sides. Neither `logicalAxiomLeaf_nat_iff` nor
`theoryAxiomLeaf_nat_iff` is used here, and no nonstandard extension is
identified with an external predicate. -/

theorem lineCheck_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Th : PRTheoryPresentation) (q i : V) :
    Semiformula.Evalb (M := V)
        ![q, i] (lineCheck Th).val ↔
      ∃ ci : V,
        Semiformula.Evalb (M := V)
          ![ci, q, i] nthDef.val ∧
        (Semiformula.Evalb (M := V)
            ![ci] (logicalAxiomLeaf Th).val ∨
         Semiformula.Evalb (M := V)
            ![ci] (theoryAxiomLeaf Th).val ∨
         ∃ j : V, j < i ∧
         ∃ k : V, k < i ∧
         ∃ cj : V,
           Semiformula.Evalb (M := V)
             ![cj, q, j] nthDef.val ∧
         ∃ ck : V,
           Semiformula.Evalb (M := V)
             ![ck, q, k] nthDef.val ∧
           Semiformula.Evalb (M := V)
             ![ck, cj, ci] impGraph.val) := by
  simp [lineCheck]

/-! ### Standard-natural-number adequacy

The outer range conjunct is essential and is not cosmetic: `nthDef` is
zero-default, so out of range the checker can still be satisfied, while
`LineJustifiedCodeNF` carries `i < q.length`. The equivalence is therefore
stated between the conjunction and the reduced line predicate.

The MP clause is preserved in the form
`q.getD k 0 = imp (q.getD j 0) (q.getD i 0)`. -/

theorem lineCheck_nat_iff
    (Th : PRTheoryPresentation) (q : List ℕ) (i : ℕ) :
    (i < q.length ∧
      Semiformula.Evalb (M := ℕ)
        ![natVecOfList q, i] (lineCheck Th).val) ↔
      LineJustifiedCodeNF Th.toTheory q i := by
  rw [lineCheck_iff, LineJustifiedCodeNF]
  constructor
  · rintro ⟨hi, ci, hci, hcase⟩
    refine ⟨hi, ?_⟩
    have hci' : ci = q.getD i 0 :=
      (nthDef_nat_iff ci q i).mp hci
    subst hci'
    rcases hcase with hlog | hth | ⟨j, hj, k, hk, cj, hcj, ck, hck, himp⟩
    · exact Or.inl ((logicalAxiomLeaf_nat_iff Th _).mp hlog)
    · exact Or.inr (Or.inl ((theoryAxiomLeaf_nat_iff Th _).mp hth))
    · have hcj' : cj = q.getD j 0 :=
        (nthDef_nat_iff cj q j).mp hcj
      have hck' : ck = q.getD k 0 :=
        (nthDef_nat_iff ck q k).mp hck
      subst hcj'
      subst hck'
      -- `impGraph_nat_iff` is output-first, so the arguments are
      -- `ck`, `cj`, `ci`, yielding `q.getD k 0 = imp (q.getD j 0) (q.getD i 0)`
      exact Or.inr (Or.inr
        ⟨j, hj, k, hk, (impGraph_nat_iff _ _ _).mp himp⟩)
  · rintro ⟨hi, hcase⟩
    refine ⟨hi, q.getD i 0, (nthDef_nat_iff _ q i).mpr rfl, ?_⟩
    rcases hcase with hlog | hth | ⟨j, hj, k, hk, heq⟩
    · exact Or.inl ((logicalAxiomLeaf_nat_iff Th _).mpr hlog)
    · exact Or.inr (Or.inl ((theoryAxiomLeaf_nat_iff Th _).mpr hth))
    · exact Or.inr (Or.inr
        ⟨j, hj, k, hk, q.getD j 0, (nthDef_nat_iff _ q j).mpr rfl,
         q.getD k 0, (nthDef_nat_iff _ q k).mpr rfl,
         (impGraph_nat_iff _ _ _).mpr heq⟩)

/-! ### All-model last element with fallback zero

The value first takes the final one-element suffix and then reads its first
entry. For the nil Vec both component operations return zero. The fixed graph is
composed from `takeLastDef` and `nthDef`, independently of `lastValue`. -/

noncomputable def lastValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (v : V) : V :=
  nth (takeLast v 1) 0

/-- Fixed graph with order `#0` output, `#1` input Vec.

The sole witness is `t = takeLast v 1`; the final atom states
`y = nth t 0`. -/
noncomputable def lastGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y v. ∃ t, !takeLastDef t v 1 ∧ !nthDef y t 0”

theorem lastGraph_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y v : V) :
    Semiformula.Evalb (M := V)
        ![y, v] lastGraph.val ↔
      ∃ t : V,
        Semiformula.Evalb (M := V)
          ![t, v, (1 : V)] takeLastDef.val ∧
        Semiformula.Evalb (M := V)
          ![y, t, (0 : V)] nthDef.val := by
  simp [lastGraph]

theorem lastGraph_iff_lastValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y v : V) :
    Semiformula.Evalb (M := V)
        ![y, v] lastGraph.val ↔
      y = lastValue v := by
  rw [lastGraph_iff]
  constructor
  · rintro ⟨t, ht, hy⟩
    have ht' : t = takeLast v 1 := by
      simpa using ht
    have hy' : y = nth t 0 := by
      simpa using hy
    rw [hy', ht', lastValue]
  · rintro rfl
    exact
      ⟨takeLast v 1, by simp, by simp [lastValue]⟩

theorem lastValue_spec
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (v : V) :
    Semiformula.Evalb (M := V)
      ![lastValue v, v] lastGraph.val := by
  exact
    (lastGraph_iff_lastValue
      (lastValue v) v).mpr rfl

theorem lastGraph_existsUnique
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (v : V) :
    ∃! y : V,
      Semiformula.Evalb (M := V)
        ![y, v] lastGraph.val := by
  refine
    ⟨lastValue v, lastValue_spec v, ?_⟩
  intro y hy
  exact
    (lastGraph_iff_lastValue y v).mp hy

theorem lastValue_defined
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    𝚺₁-Function₁[V]
      (lastValue (V := V)) via lastGraph :=
  .mk fun w ↦ by
    change
      Semiformula.Evalb (M := V)
          w lastGraph.val ↔
        w 0 = lastValue (w 1)
    rw [
      show w = ![w 0, w 1]
        from Matrix.fun_eq_vec_two w
    ]
    exact
      lastGraph_iff_lastValue
        (V := V) (w 0) (w 1)

instance lastValue_definable
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    𝚺₁-Function₁[V]
      (lastValue (V := V)) :=
  lastValue_defined.to_definable

/-! ### Standard-model agreement

The proof is an external induction on the external list only. It splits the
tail into nil and nonempty cases so that `takeLast_adjoin` and
`List.getLastD_cons` follow the same recursion. No subtraction occurs. -/

theorem lastValue_natVecOfList
    (xs : List ℕ) :
    lastValue (natVecOfList xs) =
      xs.getLastD 0 := by
  induction xs with
  | nil =>
      -- `List.getLastD_nil` was reported unused: core simp already normalizes
      -- `getLastD` through `List.getLastD_eq_getLast?`, so the rewrite cannot
      -- fire. The argument is omitted rather than the linter suppressed.
      simp [lastValue]
  | cons x xs ih =>
      cases xs with
      | nil =>
          -- Both `List.getLastD_cons` and `List.getLastD_nil` were reported
          -- unused here, for the same reason; omitted.
          simp [lastValue, takeLast_adjoin]
      | cons y ys =>
          simpa [lastValue, takeLast_adjoin,
            List.getLastD_cons] using ih

theorem lastGraph_nat_iff
    (y : ℕ) (xs : List ℕ) :
    Semiformula.Evalb (M := ℕ)
        ![y, natVecOfList xs] lastGraph.val ↔
      y = xs.getLastD 0 := by
  rw [
    lastGraph_iff_lastValue,
    lastValue_natVecOfList
  ]

def LineJustifiedNF
    (Th : TheoryPresentation) (Ψ : ProofSequence) (i : ℕ) : Prop :=
  i < Ψ.length ∧
    (Th.syn.logicalAxiom.Holds (Ψ.getD i []) ∨
     Th.ax.Holds (Ψ.getD i []) ∨
     ∃ j < i, ∃ k < i,
       Ψ.getD k [] = impString (Ψ.getD j []) (Ψ.getD i []))

/-- `IsProofList` with the reduced line predicate. -/
def IsProofListNF
    (Th : TheoryPresentation) (Ψ : ProofSequence)
    (φ : FormulaString) : Prop :=
  Ψ ≠ [] ∧
  Ψ.getLastD [] = φ ∧
  ∀ i, i < Ψ.length → LineJustifiedNF Th Ψ i

/-- The reduced proof-list predicate on a list of numerical formula codes. -/
def CodeProofNF
    (Th : TheoryPresentation) (q : List ℕ) (a : ℕ) : Prop :=
  q ≠ [] ∧
  q.getLastD 0 = a ∧
  ∀ i, i < q.length → LineJustifiedCodeNF Th q i

/-! ### Global recovery of formula status

The sole induction of this file. Formula status is not recoverable at an
isolated line; it is recoverable at every line of a complete reduced proof list,
by strong induction on the line index. -/

/-- Every line of a complete reduced proof list is a formula.

The three cases use exactly the three presentation fields:
`logicalAxiom_formula`, `ax_formula`, and the forward direction of
`formula_imp_iff` at the earlier implication line `k`. -/
private theorem formula_recovery
    (Th : TheoryPresentation) (Ψ : ProofSequence)
    (h : ∀ i, i < Ψ.length → LineJustifiedNF Th Ψ i) :
    ∀ i, i < Ψ.length → Th.syn.formula.Holds (Ψ.getD i []) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨-, hcase⟩ := h i hi
    rcases hcase with hla | hax | ⟨j, _, k, hk, heq⟩
    · exact Th.syn.logicalAxiom_formula hla
    · exact Th.ax_formula hax
    · -- the earlier implication line `k` is in range, so the induction
      -- hypothesis applies to it; `j` is not used here
      have hkl : k < Ψ.length := Nat.lt_trans hk hi
      have hfk : Th.syn.formula.Holds (Ψ.getD k []) := ih k hk hkl
      rw [heq] at hfk
      exact ((Th.syn.formula_imp_iff _ _).mp hfk).2

/-! ### The global normalization theorem -/

/-- Dropping the formula-validity conjunct from every line does not change the
proof-list predicate. The forward direction drops a conjunct; the reverse
direction restores it by `formula_recovery`. -/
theorem isProofList_iff_isProofListNF
    (Th : TheoryPresentation) (Ψ : ProofSequence) (φ : FormulaString) :
    IsProofList Th Ψ φ ↔ IsProofListNF Th Ψ φ := by
  constructor
  · rintro ⟨hne, hlast, hj⟩
    refine ⟨hne, hlast, ?_⟩
    intro i hi
    obtain ⟨hr, -, hcase⟩ := hj i hi
    exact ⟨hr, hcase⟩
  · rintro ⟨hne, hlast, hj⟩
    refine ⟨hne, hlast, ?_⟩
    intro i hi
    obtain ⟨hr, hcase⟩ := hj i hi
    exact ⟨hr, formula_recovery Th Ψ hj i hi, hcase⟩

/-! ### Decoder facts used by the code normalization

Neither of these exists in the pinned project source. `decodeFormula_zero` is
what makes the mapped defaults of `List.getD_map` and `List.getLastD_map` line
up with the literal `[]` default of the string-level predicates. -/

/-- The empty string is the decoding of the numerical code `0`. Proved from
`decodeFormula` and `listDecode_zero`, not by `rfl`. -/
private theorem decodeFormula_zero : decodeFormula 0 = [] := by
  change listDecode 0 = []
  exact listDecode_zero

/-- Decoder injectivity, derived locally from `encodeFormula_decodeFormula`.
There is no theorem named `decodeFormula_injective` in the pinned source. -/
private theorem decodeFormula_inj {x y : ℕ} :
    decodeFormula x = decodeFormula y ↔ x = y := by
  constructor
  · intro h
    have h' := congrArg encodeFormula h
    rwa [encodeFormula_decodeFormula, encodeFormula_decodeFormula] at h'
  · intro h
    rw [h]

/-- An equality between a decoded code and a decoded implication string is
exactly the corresponding numerical equality. Uses `decodeFormula_imp` and
decoder injectivity. -/
private theorem decodeFormula_eq_impString_iff {x y z : ℕ} :
    decodeFormula x = impString (decodeFormula y) (decodeFormula z) ↔
      x = imp y z := by
  rw [← decodeFormula_imp]
  exact decodeFormula_inj

/-- Indexing commutes with the decoder map, with the default `[]` supplied by
`decodeFormula_zero`.

`List.getD_map` is a Mathlib lemma in `Mathlib.Data.List.GetD`, which is not in
this file's import closure — the only import is
`Metamath.Feferman.ProofCode`. Its three-lemma proof is reproduced here from
Lean core alone: `List.getD_eq_getElem?_getD`, `List.getElem?_map`, and
`Option.getD_map`. No induction is used. -/
private theorem getD_map_decodeFormula (q : List ℕ) (i : ℕ) :
    (q.map decodeFormula).getD i [] = decodeFormula (q.getD i 0) := by
  have h :
      (q.map decodeFormula).getD i (decodeFormula 0) =
        decodeFormula (q.getD i 0) := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      Option.getD_map]
  rwa [decodeFormula_zero] at h

/-- The last entry commutes with the decoder map, with the same default. -/
private theorem getLastD_map_decodeFormula (q : List ℕ) :
    (q.map decodeFormula).getLastD [] = decodeFormula (q.getLastD 0) := by
  have h := List.getLastD_map (f := decodeFormula) (l := q) (a := (0 : ℕ))
  rwa [decodeFormula_zero] at h

/-! ### The code normalization -/

/-- The reduced line predicate on a decoded list is the numerical reduced line
predicate on the underlying code list. -/
private theorem lineJustifiedNF_map_iff
    (Th : TheoryPresentation) (q : List ℕ) (i : ℕ) :
    LineJustifiedNF Th (q.map decodeFormula) i ↔
      LineJustifiedCodeNF Th q i := by
  unfold LineJustifiedNF LineJustifiedCodeNF
  simp only [List.length_map, getD_map_decodeFormula,
    decodeFormula_eq_impString_iff]

/-- The reduced proof-list predicate on a decoded list is the numerical reduced
proof-list predicate on the underlying code list. -/
private theorem isProofListNF_map_iff
    (Th : TheoryPresentation) (q : List ℕ) (a : ℕ) :
    IsProofListNF Th (q.map decodeFormula) (decodeFormula a) ↔
      CodeProofNF Th q a := by
  unfold IsProofListNF CodeProofNF
  simp only [ne_eq, List.map_eq_nil_iff, List.length_map,
    getLastD_map_decodeFormula, decodeFormula_inj,
    lineJustifiedNF_map_iff]

/-- The numerical proof predicate normalizes to the reduced checker on the
decoded code list. `Proof_T` itself is unchanged. -/
theorem proof_T_iff_codeProofNF
    (Th : TheoryPresentation) (p a : ℕ) :
    Proof_T Th p a ↔ CodeProofNF Th (listDecode p) a := by
  change IsProofList Th (decodeProof p) (decodeFormula a) ↔ _
  rw [isProofList_iff_isProofListNF]
  change
    IsProofListNF Th ((listDecode p).map decodeFormula) (decodeFormula a) ↔ _
  exact isProofListNF_map_iff Th (listDecode p) a

/-! ### F1: the binary structural proof graph

Binary, with `#0 = p` the numerical proof-sequence code and `#1 = a` the target
numerical formula code.

Existential witness order is `q`, then `l`, then `z`. The bounded line variable
`i` follows and is not an existential witness.

Component argument orders, all output-first:

    listDecodeGraph q p     q is the decoded internal Vec of p
    lenDef          l q     l is the length of q
    lastGraph       z q     z is the final entry of q
    lineCheck       q i     the reduced line checker at line i

Nonemptiness is asserted on the decoded internal Vec as `q ≠ 0`, not on the
numerical code `p`. The final entry is obtained by `lastGraph`, not by
subtraction together with `nthDef`. The quantifier over lines is bounded by `l`,
never unbounded. -/

noncomputable def proofGraph
    (Th : PRTheoryPresentation) : 𝚺₁.Semisentence 2 :=
  let check : 𝚺₁.Semisentence 2 := lineCheck Th
  .mkSigma
    “p a.
      ∃ q, !listDecodeGraph q p ∧
        q ≠ 0 ∧
        ∃ l, !lenDef l q ∧
          ∃ z, !lastGraph z q ∧
            z = a ∧
            ∀ i < l, !check q i”

/-- Literal quotation expansion, kept private. The public normal form below
eliminates the three functional witnesses. -/
private theorem proofGraph_raw_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Th : PRTheoryPresentation) (p a : V) :
    Semiformula.Evalb (M := V)
        ![p, a] (proofGraph Th).val ↔
      ∃ q : V,
        Semiformula.Evalb (M := V)
          ![q, p] listDecodeGraph.val ∧
        q ≠ 0 ∧
        ∃ l : V,
          Semiformula.Evalb (M := V)
            ![l, q] lenDef.val ∧
          ∃ z : V,
            Semiformula.Evalb (M := V)
              ![z, q] lastGraph.val ∧
            z = a ∧
            ∀ i : V, i < l →
              Semiformula.Evalb (M := V)
                ![q, i] (lineCheck Th).val := by
  simp [proofGraph]

/-! ### All-model normal form

The three functional witnesses are eliminated against their selected values:
`q` against `listDecodeValue p`, `l` against `len`, and `z` against
`lastValue`. `lineCheck` is deliberately left as an opaque evaluation atom —
`lineCheck_iff` is not used — so neither arithmetized axiom leaf receives a
nonstandard interpretation here. -/

theorem proofGraph_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Th : PRTheoryPresentation) (p a : V) :
    Semiformula.Evalb (M := V)
        ![p, a] (proofGraph Th).val ↔
      listDecodeValue p ≠ 0 ∧
      lastValue (listDecodeValue p) = a ∧
      ∀ i : V, i < len (listDecodeValue p) →
        Semiformula.Evalb (M := V)
          ![listDecodeValue p, i] (lineCheck Th).val := by
  rw [proofGraph_raw_iff]
  constructor
  · rintro ⟨q, hq, hqne, l, hl, z, hz, hza, hlines⟩
    have hq' : q = listDecodeValue p :=
      (listDecodeGraph_iff_listDecodeValue q p).mp hq
    subst hq'
    -- `subst` has eliminated `q` in favour of `listDecodeValue p`
    have hl' : l = len (listDecodeValue p) := by simpa using hl
    subst hl'
    have hz' : z = lastValue (listDecodeValue p) :=
      (lastGraph_iff_lastValue _ _).mp hz
    subst hz'
    exact ⟨hqne, hza, hlines⟩
  · rintro ⟨hne, hlast, hlines⟩
    refine
      ⟨listDecodeValue p, listDecodeValue_spec p, hne,
       len (listDecodeValue p), by simp,
       lastValue (listDecodeValue p),
         (lastGraph_iff_lastValue _ _).mpr rfl,
       hlast, hlines⟩

/-! ### Standard nonemptiness and length bridges

Case analysis, not a new induction. Foundation's `adjoin_ne_zero` is `[simp]`,
so the cons case closes immediately. -/

private theorem natVecOfList_ne_zero_iff (q : List ℕ) :
    natVecOfList q ≠ 0 ↔ q ≠ [] := by
  cases q <;> simp

private theorem lenDef_nat_iff (l : ℕ) (q : List ℕ) :
    Semiformula.Evalb (M := ℕ)
        ![l, natVecOfList q] lenDef.val ↔
      l = q.length := by
  simpa only [len_natVecOfList] using
    (show
      Semiformula.Evalb (M := ℕ)
          ![l, natVecOfList q] lenDef.val ↔
        l = len (natVecOfList q)
      from by simp)

/-! ### Standard-model adequacy against the code-level checker

At each bounded line the range-sensitive B8R14 theorem is used in both
directions. `lineCheck_nat_iff` is never used as a bare pointwise equivalence:
its left-hand side carries the range conjunct, which is false outside the list
range because `nthDef` is zero-default. -/

theorem proofGraph_nat_iff_codeProofNF
    (Th : PRTheoryPresentation) (p a : ℕ) :
    Semiformula.Evalb (M := ℕ)
        ![p, a] (proofGraph Th).val ↔
      CodeProofNF Th.toTheory
        (Metamath.Feferman.listDecode p) a := by
  rw [proofGraph_iff, CodeProofNF, listDecodeValue_nat,
    natVecOfList_ne_zero_iff, lastValue_natVecOfList, len_natVecOfList]
  constructor
  · rintro ⟨hne, hlast, hlines⟩
    refine ⟨hne, hlast, ?_⟩
    intro i hi
    exact (lineCheck_nat_iff Th (Metamath.Feferman.listDecode p) i).mp
      ⟨hi, hlines i hi⟩
  · rintro ⟨hne, hlast, hlines⟩
    refine ⟨hne, hlast, ?_⟩
    intro i hi
    exact ((lineCheck_nat_iff Th (Metamath.Feferman.listDecode p) i).mpr
      (hlines i hi)).2

/-! ### Final standard-model adequacy

The second step is exactly the accepted B8R12 normalization bridge; no
normalization is re-proved here. -/

theorem proofGraph_nat_iff
    (Th : PRTheoryPresentation) (p a : ℕ) :
    Semiformula.Evalb (M := ℕ)
        ![p, a] (proofGraph Th).val ↔
      Proof_T Th.toTheory p a := by
  calc
    Semiformula.Evalb (M := ℕ)
        ![p, a] (proofGraph Th).val ↔
        CodeProofNF Th.toTheory
          (Metamath.Feferman.listDecode p) a :=
      proofGraph_nat_iff_codeProofNF Th p a
    _ ↔ Proof_T Th.toTheory p a :=
      (proof_T_iff_codeProofNF Th.toTheory p a).symm

/-! ### W1: numeralwise weak representation of the same binary formula

For fixed standard naturals `p` and `a`, the numerical proof predicate holds
exactly when the ambient arithmetic theory `T` proves the positive numeral
instance of the binary structural formula. `T` is distinct from
`Th.toTheory`.

A false instance yields non-derivability of this positive sentence. It does not
yield derivability of its negation. This is not a uniform object-language
closure theorem. -/

theorem proofGraph_weak_representation
    (Th : PRTheoryPresentation) {T : ArithmeticTheory}
    [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] (p a : ℕ) :
    Proof_T Th.toTheory p a ↔
      T ⊢ ((proofGraph Th).val/[p, a]) := by
  calc
    Proof_T Th.toTheory p a ↔
        Semiformula.Evalb (M := ℕ) ![p, a] (proofGraph Th).val :=
      (proofGraph_nat_iff Th p a).symm
    _ ↔ ℕ↓[ℒₒᵣ] ⊧ ((proofGraph Th).val/[p, a]) := by
      -- Substitution semantics identifies the two evaluation environments,
      -- `![p, a]` against `Semiterm.val … ∘ ![↑p, ↑a]`. `Function.comp_def`
      -- must NOT be supplied here: turning the composition into a lambda blocks
      -- simp's own handling and leaves a residual `Fin 2` function equality.
      -- The formula itself is never unfolded.
      simp [models_iff, Semiformula.eval_substs]
    _ ↔ T ⊢ ((proofGraph Th).val/[p, a]) := by
      -- `apply` first, so the sentence is assigned from the goal rather than
      -- inferred from the argument's type. Supplying the argument in term
      -- position forces `whnf` on `(proofGraph Th).val`, which unfolds through
      -- `lineCheck` into the epsilon-selected axiom leaves and exhausts the
      -- default heartbeat budget.
      apply sigma_one_completeness_iff
      -- `Hierarchy.rew` transports the recorded `𝚺₁` property across the
      -- substitution. Nothing here unfolds `proofGraph`, `lineCheck`, or
      -- either axiom leaf.
      exact Hierarchy.rew _ (proofGraph Th).sigma_prop

/-! ### S1: internal Vec append length

The length of a binary internal-Vec append is the sum of the lengths, in an
arbitrary model of `𝗜𝚺₁`.

One Sigma-one adjoin induction on `xs`, with `ys` fixed as a parameter and not
generalized. `definability` discharges the motive; the nil case closes by
`simp`; the adjoin case rewrites with `vecAppendValue_adjoin`, `len_adjoin` and
the induction hypothesis, then finishes by right commutativity. -/

@[simp] theorem len_vecAppendValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (xs ys : V) :
    len (vecAppendValue xs ys) = len xs + len ys := by
  induction xs using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin x xs ih =>
    simp only [vecAppendValue_adjoin, len_adjoin, ih]
    exact add_right_comm _ _ _

/-! ### S2: internal Vec append left-prefix lookup

At an index strictly inside the left operand, reading a binary internal-Vec
append returns the left operand's entry, in an arbitrary model of `𝗜𝚺₁`.

This mirrors the pinned Foundation proof of `concat_nth_lt`
(`Foundation/FirstOrder/Arithmetic/HFS/Vec.lean:863`) with `concat` replaced by
`vecAppendValue`. One Sigma-one adjoin induction on the internal Vec `xs`, with
`ys` fixed as a parameter and the index `i` generalized. `definability`
discharges the Sigma-one motive. The nil case is vacuous because `i < len 0` is
absurd. In the adjoin case `zero_or_succ i` splits into the head lookup and the
recursive tail lookup.

S1's `len_vecAppendValue` is inherited and available, but is intentionally not
used here. Deliberately not marked `@[simp]`. -/

theorem vecAppendValue_nth_lt
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (xs ys : V) {i : V}
    (hi : i < len xs) :
    (vecAppendValue xs ys).[i] = xs.[i] := by
  induction xs using adjoin_ISigma1.sigma1_succ_induction generalizing i
  · definability
  case nil => simp at hi
  case adjoin x xs ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simp [ih (by simpa using hi)]

/-! ### S3: internal Vec append shifted-right lookup

At an index shifted past the whole left operand, reading a binary internal-Vec
append returns the right operand's entry, in an arbitrary model of `𝗜𝚺₁`.

The statement is deliberately **unconditional**: no `i < len ys` hypothesis is
imposed, because internal `nth` is total and zero-default, so the identity holds
at every internal index — beyond `len ys` both sides are `0`.

One Sigma-one adjoin induction on the internal Vec `xs`, with both `ys` and `i`
fixed; nothing is generalized. `definability` discharges the Sigma-one motive.
The nil case closes by `simp`. In the adjoin case the arithmetic normalization
`add_right_comm (len xs) 1 i` turns `(len xs + 1) + i` into `(len xs + i) + 1`,
which is precisely what exposes `nth_adjoin_succ`; the induction hypothesis then
closes the goal.

This generalizes Foundation's unconditional `@[simp] concat_nth_len`
(`Foundation/FirstOrder/Arithmetic/HFS/Vec.lean:872`), which reads only the
single appended element at index `len v`.

S1's `len_vecAppendValue` and S2's `vecAppendValue_nth_lt` are inherited and
available, but neither is used here. -/

@[simp] theorem vecAppendValue_nth_len_add
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (xs ys i : V) :
    (vecAppendValue xs ys).[len xs + i] = ys.[i] := by
  induction xs using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin x xs ih =>
    rw [vecAppendValue_adjoin, len_adjoin,
      add_right_comm (len xs) 1 i, nth_adjoin_succ]
    exact ih
/-! ### All-model drop on internal Vecs

Retain the final `len v - n` entries. Foundation's subtraction is truncated, so
an index past the end gives the nil Vec. The fixed graph is composed from
`lenDef`, `subDef` and `takeLastDef`, independently of `dropValue`. -/

noncomputable def dropValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (v n : V) : V :=
  takeLast v (len v - n)

/-- Fixed graph with order `#0` output Vec, `#1` input Vec, `#2` number dropped.

Witnesses in order: `l = len v`, `k = l - n`, `y = takeLast v k`. -/
noncomputable def dropGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y v n.
    ∃ l, !lenDef l v ∧
    ∃ k, !subDef k l n ∧
      !takeLastDef y v k”

theorem dropGraph_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y v n : V) :
    Semiformula.Evalb (M := V)
        ![y, v, n] dropGraph.val ↔
      ∃ l : V,
        Semiformula.Evalb (M := V)
          ![l, v] lenDef.val ∧
      ∃ k : V,
        Semiformula.Evalb (M := V)
          ![k, l, n] subDef.val ∧
        Semiformula.Evalb (M := V)
          ![y, v, k] takeLastDef.val := by
  simp [dropGraph]

theorem dropGraph_iff_dropValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y v n : V) :
    Semiformula.Evalb (M := V)
        ![y, v, n] dropGraph.val ↔
      y = dropValue v n := by
  rw [dropGraph_iff]
  constructor
  · rintro ⟨l, hl, k, hk, hy⟩
    have hl' : l = len v := by
      simpa using hl
    have hk' : k = l - n := by
      simpa using hk
    have hy' : y = takeLast v k := by
      simpa using hy
    rw [hy', hk', hl', dropValue]
  · rintro rfl
    exact
      ⟨len v, by simp,
       len v - n, by simp,
       by simp [dropValue]⟩

theorem dropValue_spec
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (v n : V) :
    Semiformula.Evalb (M := V)
      ![dropValue v n, v, n] dropGraph.val := by
  exact
    (dropGraph_iff_dropValue
      (dropValue v n) v n).mpr rfl

theorem dropGraph_existsUnique
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (v n : V) :
    ∃! y : V,
      Semiformula.Evalb (M := V)
        ![y, v, n] dropGraph.val := by
  refine
    ⟨dropValue v n, dropValue_spec v n, ?_⟩
  intro y hy
  exact
    (dropGraph_iff_dropValue y v n).mp hy

theorem dropValue_defined
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    𝚺₁-Function₂[V]
      (dropValue (V := V)) via dropGraph :=
  .mk fun w ↦ by
    change
      Semiformula.Evalb (M := V)
          w dropGraph.val ↔
        w 0 = dropValue (w 1) (w 2)
    rw [
      show w = ![w 0, w 1, w 2]
        from Matrix.fun_eq_vec_three w
    ]
    exact
      dropGraph_iff_dropValue
        (V := V) (w 0) (w 1) (w 2)

instance dropValue_definable
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    𝚺₁-Function₂[V]
      (dropValue (V := V)) :=
  dropValue_defined.to_definable

/-! ### Standard-model agreement

One external induction on the external list, generalizing the index, and one
case split on the index. The successor branch cancels the two `+ 1` summands
with `add_sub_add` inside Foundation's subtraction, so no identification of that
subtraction with `Nat.sub` is required. -/

theorem dropValue_natVecOfList
    (xs : List ℕ) (n : ℕ) :
    dropValue (natVecOfList xs) n =
      natVecOfList (xs.drop n) := by
  induction xs generalizing n with
  | nil =>
      simp [dropValue]
  | cons x xs ih =>
      cases n with
      | zero =>
          -- `simp` normalizes `len (x ∷ w)` to `len w + 1` before
          -- `takeLast_len_self` can match, so the rewrites are named directly.
          -- `sub_zero` is qualified: the bare name is ambiguous against
          -- Mathlib's `_root_.sub_zero`.
          simp only [dropValue, Arithmetic.sub_zero, takeLast_len_self,
            List.drop_zero]
      | succ n =>
          -- `add_sub_add` cancels the two `+ 1` summands inside Foundation's
          -- subtraction. The branch condition is refuted by `sub_le_self`,
          -- qualified against Mathlib's `_root_.sub_le_self`.
          --
          -- The refutation deliberately uses only `Arithmetic.*` lemmas. At
          -- `V = ℕ` Foundation's `≤` is the scoped `x = y ∨ x < y`
          -- (PeanoMinus/Basic.lean:173-175), which is not `Nat.le`, while the
          -- `<` in the branch condition is the `ORingStructure` one. Every
          -- generic Mathlib order lemma -- `not_lt`, `lt_of_lt_of_le`,
          -- `lt_irrefl` -- resolves its instance to `Nat.instLinearOrder` or
          -- `Nat.instPreorder` and then fails to accept Foundation's `≤`.
          -- Unfolding through `le_def` and closing with `Arithmetic.lt_trans`
          -- and `Arithmetic.lt_irrefl` never leaves Foundation's instance, so
          -- no subtraction bridge between the two is needed.
          rw [dropValue, natVecOfList_cons, len_adjoin, add_sub_add,
              takeLast_adjoin,
              ite_eq_right (by
                intro h
                rcases Arithmetic.le_def.mp
                    (Arithmetic.sub_le_self (V := ℕ)
                      (len (natVecOfList xs)) n) with he | hl
                · rw [he] at h
                  exact Arithmetic.lt_irrefl _ h
                · exact Arithmetic.lt_irrefl _
                    (Arithmetic.lt_trans _ _ _ h hl)),
              List.drop_succ_cons]
          exact ih n

theorem dropGraph_nat_iff
    (y : ℕ) (xs : List ℕ) (n : ℕ) :
    Semiformula.Evalb (M := ℕ)
        ![y, natVecOfList xs, n] dropGraph.val ↔
      y = natVecOfList (xs.drop n) := by
  rw [
    dropGraph_iff_dropValue,
    dropValue_natVecOfList
  ]


/-! ### All-model internal `rhsString`

Drop the first two entries, then drop as many further entries as the length
field at index `1` of the ORIGINAL input records. The nesting of the project
definition is preserved, not collapsed into a single offset. -/

noncomputable def rhsStringValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (v : V) : V :=
  dropValue (dropValue v 2) (nth v 1)

/-- Fixed graph with order `#0` output Vec, `#1` input Vec.

Witnesses in order: `t = dropValue v 2`, `n = nth v 1`, `y = dropValue t n`.
The `nthDef` atom indexes `v`, not `t`. -/
noncomputable def rhsStringGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y v.
    ∃ t, !dropGraph t v 2 ∧
    ∃ n, !nthDef n v 1 ∧
      !dropGraph y t n”

theorem rhsStringGraph_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y v : V) :
    Semiformula.Evalb (M := V)
        ![y, v] rhsStringGraph.val ↔
      ∃ t : V,
        Semiformula.Evalb (M := V)
          ![t, v, (2 : V)] dropGraph.val ∧
      ∃ n : V,
        Semiformula.Evalb (M := V)
          ![n, v, (1 : V)] nthDef.val ∧
        Semiformula.Evalb (M := V)
          ![y, t, n] dropGraph.val := by
  simp [rhsStringGraph]

theorem rhsStringGraph_iff_rhsStringValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y v : V) :
    Semiformula.Evalb (M := V)
        ![y, v] rhsStringGraph.val ↔
      y = rhsStringValue v := by
  rw [rhsStringGraph_iff]
  constructor
  · rintro ⟨t, ht, n, hn, hy⟩
    have ht' : t = dropValue v 2 :=
      (dropGraph_iff_dropValue t v 2).mp ht
    have hn' : n = nth v 1 := by
      simpa using hn
    have hy' : y = dropValue t n :=
      (dropGraph_iff_dropValue y t n).mp hy
    rw [hy', ht', hn', rhsStringValue]
  · rintro rfl
    exact
      ⟨dropValue v 2,
       (dropGraph_iff_dropValue _ v 2).mpr rfl,
       nth v 1, by simp,
       (dropGraph_iff_dropValue _ _ _).mpr rfl⟩

theorem rhsStringValue_spec
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (v : V) :
    Semiformula.Evalb (M := V)
      ![rhsStringValue v, v] rhsStringGraph.val := by
  exact
    (rhsStringGraph_iff_rhsStringValue
      (rhsStringValue v) v).mpr rfl

theorem rhsStringGraph_existsUnique
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (v : V) :
    ∃! y : V,
      Semiformula.Evalb (M := V)
        ![y, v] rhsStringGraph.val := by
  refine
    ⟨rhsStringValue v, rhsStringValue_spec v, ?_⟩
  intro y hy
  exact
    (rhsStringGraph_iff_rhsStringValue y v).mp hy

theorem rhsStringValue_defined
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    𝚺₁-Function₁[V]
      (rhsStringValue (V := V)) via rhsStringGraph :=
  .mk fun w ↦ by
    change
      Semiformula.Evalb (M := V)
          w rhsStringGraph.val ↔
        w 0 = rhsStringValue (w 1)
    rw [
      show w = ![w 0, w 1]
        from Matrix.fun_eq_vec_two w
    ]
    exact
      rhsStringGraph_iff_rhsStringValue
        (V := V) (w 0) (w 1)

instance rhsStringValue_definable
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    𝚺₁-Function₁[V]
      (rhsStringValue (V := V)) :=
  rhsStringValue_defined.to_definable

/-! ### Standard-model agreement

The three accepted component bridges are composed in the same nesting order as
the value. No induction, no `List.drop_drop`, no collapsed offset. -/

theorem rhsStringValue_natVecOfList
    (xs : List ℕ) :
    rhsStringValue (natVecOfList xs) =
      natVecOfList
        (Metamath.Feferman.rhsString xs) := by
  rw [
    rhsStringValue,
    dropValue_natVecOfList,
    nth_natVecOfList,
    dropValue_natVecOfList,
    Metamath.Feferman.rhsString
  ]
  -- Both sides are now syntactically identical, but `rw`'s trailing `rfl` runs
  -- at reducible transparency and does not close it; an explicit `rfl` does.
  rfl

theorem rhsStringGraph_nat_iff
    (y : ℕ) (xs : List ℕ) :
    Semiformula.Evalb (M := ℕ)
        ![y, natVecOfList xs] rhsStringGraph.val ↔
      y =
        natVecOfList
          (Metamath.Feferman.rhsString xs) := by
  rw [
    rhsStringGraph_iff_rhsStringValue,
    rhsStringValue_natVecOfList
  ]


/-! ### Structural correctness of `rhsStringValue` on implication strings

Arbitrary model, arbitrary internal Vecs, no well-formedness hypothesis, and no
appeal to standard-model agreement. -/

theorem dropValue_adjoin_succ
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (x v n : V) :
    dropValue (x ∷ v) (n + 1) =
      dropValue v n := by
  change
    takeLast (x ∷ v)
        (len (x ∷ v) - (n + 1)) =
      takeLast v (len v - n)
  rw [
    len_adjoin,
    add_sub_add,
    takeLast_adjoin,
    ite_eq_right (by
      intro h
      rcases Arithmetic.le_def.mp
          (Arithmetic.sub_le_self
            (V := V) (len v) n) with he | hl
      · rw [he] at h
        exact Arithmetic.lt_irrefl _ h
      · exact Arithmetic.lt_irrefl _
          (Arithmetic.lt_trans _ _ _ h hl))
  ]

theorem dropValue_vecAppendValue_len
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a b : V) :
    dropValue (vecAppendValue a b) (len a) =
      b := by
  induction a using
      adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil =>
    simp only [
      vecAppendValue_nil,
      len_nil,
      dropValue,
      Arithmetic.sub_zero,
      takeLast_len_self
    ]
  case adjoin x a ih =>
    rw [
      vecAppendValue_adjoin,
      len_adjoin,
      dropValue_adjoin_succ,
      ih
    ]

theorem rhsStringValue_impStringValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a b : V) :
    rhsStringValue (impStringValue a b) =
      b := by
  simp only [
    rhsStringValue,
    impStringValue,
    nth_adjoin_one,
    nth_adjoin_zero
  ]
  -- `simp` cannot decompose the `ORingStructure` numeral `2` at an arbitrary
  -- model. This is Foundation's own idiom for the same step; see
  -- `PeanoMinus/Basic.lean:430`, `show (2 : M) = 1 + 1 from
  -- one_add_one_eq_two.symm`.
  have htwo : (2 : V) = (1 : V) + 1 :=
    one_add_one_eq_two.symm
  rw [htwo, dropValue_adjoin_succ]
  have hone : (1 : V) = (0 : V) + 1 := by
    simp
  rw [hone, dropValue_adjoin_succ]
  have hzero :
      dropValue (vecAppendValue a b) (0 : V) =
        vecAppendValue a b := by
    simp only [
      dropValue,
      Arithmetic.sub_zero,
      takeLast_len_self
    ]
  rw [
    hzero,
    dropValue_vecAppendValue_len
  ]


/-! ### Numerical right-hand side, all-model

The numerical operation decodes a formula code to an internal Vec, applies the
already-verified internal `rhsStringValue`, and encodes the resulting Vec. No
new selector, decoder, recursion construction, or direct choice is introduced.
-/

noncomputable def rhsValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a : V) : V :=
  listEncodeValue
    (rhsStringValue
      (listDecodeValue a))

/-- Fixed graph with order `#0` output numerical formula code and `#1` input
numerical formula code.

Witnesses occur in the order `da = listDecodeValue a`,
`ds = rhsStringValue da`, and `y = listEncodeValue ds`. Every component graph
retains its established output-first argument order. -/
noncomputable def rhsGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y a.
    ∃ da, !listDecodeGraph da a ∧
    ∃ ds, !rhsStringGraph ds da ∧
      !listEncodeGraph y ds”

theorem rhsGraph_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y a : V) :
    Semiformula.Evalb (M := V)
        ![y, a] rhsGraph.val ↔
      ∃ da : V,
        Semiformula.Evalb (M := V)
          ![da, a] listDecodeGraph.val ∧
      ∃ ds : V,
        Semiformula.Evalb (M := V)
          ![ds, da] rhsStringGraph.val ∧
        Semiformula.Evalb (M := V)
          ![y, ds] listEncodeGraph.val := by
  simp [rhsGraph]

theorem rhsGraph_iff_rhsValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y a : V) :
    Semiformula.Evalb (M := V)
        ![y, a] rhsGraph.val ↔
      y = rhsValue a := by
  rw [rhsGraph_iff]
  constructor
  · rintro ⟨da, hda, ds, hds, hy⟩
    have hda' : da = listDecodeValue a :=
      (listDecodeGraph_iff_listDecodeValue da a).mp hda
    have hds' : ds = rhsStringValue da :=
      (rhsStringGraph_iff_rhsStringValue ds da).mp hds
    have hy' : y = listEncodeValue ds :=
      (listEncodeGraph_iff_listEncodeValue y ds).mp hy
    rw [hy', hds', hda', rhsValue]
  · rintro rfl
    refine
      ⟨listDecodeValue a, listDecodeValue_spec a,
       rhsStringValue (listDecodeValue a),
       rhsStringValue_spec _, ?_⟩
    exact
      (listEncodeGraph_iff_listEncodeValue _ _).mpr rfl

theorem rhsValue_spec
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a : V) :
    Semiformula.Evalb (M := V)
      ![rhsValue a, a] rhsGraph.val := by
  exact
    (rhsGraph_iff_rhsValue
      (rhsValue a) a).mpr rfl

theorem rhsGraph_existsUnique
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a : V) :
    ∃! y : V,
      Semiformula.Evalb (M := V)
        ![y, a] rhsGraph.val := by
  refine
    ⟨rhsValue a,
      rhsValue_spec a, ?_⟩
  intro y hy
  exact
    (rhsGraph_iff_rhsValue y a).mp hy

theorem rhsValue_defined
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    𝚺₁-Function₁[V]
      (rhsValue (V := V)) via rhsGraph :=
  .mk fun v ↦ by
    change
      Semiformula.Evalb (M := V)
          v rhsGraph.val ↔
        v 0 = rhsValue (v 1)
    rw [
      show v = ![v 0, v 1]
        from Matrix.fun_eq_vec_two v
    ]
    exact
      rhsGraph_iff_rhsValue
        (V := V) (v 0) (v 1)

instance rhsValue_definable
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    𝚺₁-Function₁[V]
      (rhsValue (V := V)) :=
  rhsValue_defined.to_definable

/-! ### Structural correctness on numerical implication codes

The decoder left inverse first cancels decoding after encoding the implication
string. The structural `rhsString` theorem then selects the consequent string.
Finally, the decoder right inverse cancels encoding after decoding the original
consequent code.
-/

theorem rhsValue_impValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a b : V) :
    rhsValue (impValue a b) = b := by
  change
    listEncodeValue
        (rhsStringValue
          (listDecodeValue
            (listEncodeValue
              (impStringValue
                (listDecodeValue a)
                (listDecodeValue b))))) =
      b
  rw [
    listDecodeValue_leftInverse
      (V := V)
      (impStringValue
        (listDecodeValue a)
        (listDecodeValue b)),
    rhsStringValue_impStringValue
      (V := V)
      (listDecodeValue a)
      (listDecodeValue b),
    listDecodeValue_rightInverse
      (V := V) b
  ]

/-! ### Standard-model agreement

The project numerical `rhs` occurs only in this boundary section.
-/

theorem rhsValue_nat
    (a : ℕ) :
    rhsValue a =
      Metamath.Feferman.rhs a := by
  change
    listEncodeValue
        (rhsStringValue
          (listDecodeValue a)) =
      Metamath.Feferman.listEncode
        (Metamath.Feferman.rhsString
          (Metamath.Feferman.listDecode a))
  rw [
    listDecodeValue_nat a,
    rhsStringValue_natVecOfList,
    listEncodeValue_natVecOfList
  ]

theorem rhsGraph_nat_iff
    (y a : ℕ) :
    Semiformula.Evalb (M := ℕ)
        ![y, a] rhsGraph.val ↔
      y = Metamath.Feferman.rhs a := by
  rw [
    rhsGraph_iff_rhsValue,
    rhsValue_nat
  ]


/-! ### Numerical modus ponens, all-model

The operation remains entirely at the level of internal Vecs of numerical
formula codes. It decodes `r` and `p`, takes the last decoded line of `r` with
fallback zero, applies numerical `rhsValue`, appends its singleton first to the
decoded `p` and then to the decoded `r`, and finally encodes the result.

The append nesting is deliberately right-associated. At the standard-model
boundary, Lean core's `List.append_assoc` identifies its external-list
interpretation with the left-associated normalized project expression. No new or
arbitrary-model `vecAppendValue` associativity theorem is stated or used.

`List.++` is left-associative, so the project expression
`listDecode r ++ listDecode p ++ [rhs ...]` is `(_ ++ _) ++ [_]`. That is a
different nesting from the internal value, not the same one.
-/

noncomputable def mpValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (r p : V) : V :=
  listEncodeValue
    (vecAppendValue
      (listDecodeValue r)
      (vecAppendValue
        (listDecodeValue p)
        (rhsValue
          (lastValue
            (listDecodeValue r)) ∷ 0)))

/-- Fixed graph with outer order `#0` output proof-sequence code,
`#1` implication-proof code `r`, and `#2` antecedent-proof code `p`.

Witnesses occur in this order:

- `dr = listDecodeValue r`;
- `dp = listDecodeValue p`;
- `lr = lastValue dr`;
- `c = rhsValue lr`;
- `cs = c ∷ 0`;
- `pcs = vecAppendValue dp cs`;
- `lines = vecAppendValue dr pcs`;
- `y = listEncodeValue lines`.

Every component atom retains its established output-first argument order. -/
noncomputable def mpGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y r p.
    ∃ dr, !listDecodeGraph dr r ∧
    ∃ dp, !listDecodeGraph dp p ∧
    ∃ lr, !lastGraph lr dr ∧
    ∃ c, !rhsGraph c lr ∧
    ∃ cs, !adjoinDef cs c 0 ∧
    ∃ pcs, !vecAppendGraph pcs dp cs ∧
    ∃ lines, !vecAppendGraph lines dr pcs ∧
      !listEncodeGraph y lines”

theorem mpGraph_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y r p : V) :
    Semiformula.Evalb (M := V)
        ![y, r, p] mpGraph.val ↔
      ∃ dr : V,
        Semiformula.Evalb (M := V)
          ![dr, r] listDecodeGraph.val ∧
      ∃ dp : V,
        Semiformula.Evalb (M := V)
          ![dp, p] listDecodeGraph.val ∧
      ∃ lr : V,
        Semiformula.Evalb (M := V)
          ![lr, dr] lastGraph.val ∧
      ∃ c : V,
        Semiformula.Evalb (M := V)
          ![c, lr] rhsGraph.val ∧
      ∃ cs : V,
        Semiformula.Evalb (M := V)
          ![cs, c, (0 : V)] adjoinDef.val ∧
      ∃ pcs : V,
        Semiformula.Evalb (M := V)
          ![pcs, dp, cs] vecAppendGraph.val ∧
      ∃ lines : V,
        Semiformula.Evalb (M := V)
          ![lines, dr, pcs] vecAppendGraph.val ∧
        Semiformula.Evalb (M := V)
          ![y, lines] listEncodeGraph.val := by
  simp [mpGraph]

theorem mpGraph_iff_mpValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y r p : V) :
    Semiformula.Evalb (M := V)
        ![y, r, p] mpGraph.val ↔
      y = mpValue r p := by
  rw [mpGraph_iff]
  constructor
  · rintro
      ⟨dr, hdr, dp, hdp, lr, hlr, c, hc,
       cs, hcs, pcs, hpcs, lines, hlines, hy⟩
    have hdr' : dr = listDecodeValue r :=
      (listDecodeGraph_iff_listDecodeValue dr r).mp hdr
    have hdp' : dp = listDecodeValue p :=
      (listDecodeGraph_iff_listDecodeValue dp p).mp hdp
    have hlr' : lr = lastValue dr :=
      (lastGraph_iff_lastValue lr dr).mp hlr
    have hc' : c = rhsValue lr :=
      (rhsGraph_iff_rhsValue c lr).mp hc
    have hcs' : cs = c ∷ (0 : V) := by
      simpa using hcs
    have hpcs' : pcs = vecAppendValue dp cs :=
      (vecAppendGraph_iff_vecAppendValue pcs dp cs).mp hpcs
    have hlines' : lines = vecAppendValue dr pcs :=
      (vecAppendGraph_iff_vecAppendValue lines dr pcs).mp hlines
    have hy' : y = listEncodeValue lines :=
      (listEncodeGraph_iff_listEncodeValue y lines).mp hy
    rw [
      hy', hlines', hpcs', hcs', hc', hlr', hdp', hdr',
      mpValue
    ]
  · rintro rfl
    refine
      ⟨listDecodeValue r, listDecodeValue_spec r,
       listDecodeValue p, listDecodeValue_spec p,
       lastValue (listDecodeValue r),
         lastValue_spec (listDecodeValue r),
       rhsValue (lastValue (listDecodeValue r)),
         rhsValue_spec (lastValue (listDecodeValue r)),
       rhsValue (lastValue (listDecodeValue r)) ∷ (0 : V),
         by simp,
       vecAppendValue
         (listDecodeValue p)
         (rhsValue (lastValue (listDecodeValue r)) ∷ (0 : V)),
         (vecAppendGraph_iff_vecAppendValue _ _ _).mpr rfl,
       vecAppendValue
         (listDecodeValue r)
         (vecAppendValue
           (listDecodeValue p)
           (rhsValue
             (lastValue
               (listDecodeValue r)) ∷ (0 : V))),
         (vecAppendGraph_iff_vecAppendValue _ _ _).mpr rfl,
       ?_⟩
    exact
      (listEncodeGraph_iff_listEncodeValue _ _).mpr rfl

theorem mpValue_spec
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (r p : V) :
    Semiformula.Evalb (M := V)
      ![mpValue r p, r, p] mpGraph.val := by
  exact
    (mpGraph_iff_mpValue
      (mpValue r p) r p).mpr rfl

theorem mpGraph_existsUnique
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (r p : V) :
    ∃! y : V,
      Semiformula.Evalb (M := V)
        ![y, r, p] mpGraph.val := by
  refine
    ⟨mpValue r p, mpValue_spec r p, ?_⟩
  intro y hy
  exact
    (mpGraph_iff_mpValue y r p).mp hy

theorem mpValue_defined
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    𝚺₁-Function₂[V]
      (mpValue (V := V)) via mpGraph :=
  .mk fun w ↦ by
    change
      Semiformula.Evalb (M := V)
          w mpGraph.val ↔
        w 0 = mpValue (w 1) (w 2)
    rw [
      show w = ![w 0, w 1, w 2]
        from Matrix.fun_eq_vec_three w
    ]
    exact
      mpGraph_iff_mpValue
        (V := V) (w 0) (w 1) (w 2)

instance mpValue_definable
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    𝚺₁-Function₂[V]
      (mpValue (V := V)) :=
  mpValue_defined.to_definable

/-! ### Decoded output sequence

This arbitrary-model theorem exposes exactly the single-level internal Vec
encoded by `mpValue`. It uses only the accepted decoder/encoder left inverse.
It makes no implication, validity, or proof-preservation claim.
-/

theorem listDecodeValue_mpValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (r p : V) :
    listDecodeValue (mpValue r p) =
      vecAppendValue
        (listDecodeValue r)
        (vecAppendValue
          (listDecodeValue p)
          (rhsValue
            (lastValue
              (listDecodeValue r)) ∷ 0)) := by
  rw [mpValue, listDecodeValue_leftInverse]

/-! ### S4: decoded MP-output length

The internal Vec obtained by decoding an MP-extended proof-sequence code has
length equal to the sum of the two decoded input lengths plus one, in an
arbitrary model of `𝗜𝚺₁`.

Here `r` and `p` are internal numerical proof-sequence codes, `listDecodeValue r`
and `listDecodeValue p` are the internal Vecs they decode to, and `mpValue r p`
is the internal numerical code of the MP-extended sequence. The `+ 1` is the
single appended conclusion line.

The statement is **unconditional**: no length bound, no well-formedness
condition, and no proof-validity condition is imposed on `r` or `p`.

`listDecodeValue_mpValue`, inherited from B8R10, is the decoder/MP bridge; it
rewrites the decoded output into an explicit binary internal append whose right
operand is a one-element Vec. S1's `len_vecAppendValue` then applies **twice**,
once per nested append, and `len_adjoin`, `len_nil`, `zero_add` compute the
singleton length. The sum that simplification produces is right-associated, so
`(add_assoc _ _ _).symm` converts it to the left-associated form the statement
requires.

No induction, recursion, `definability`, or helper declaration is needed. S2's
`vecAppendValue_nth_lt` and S3's `vecAppendValue_nth_len_add` are inherited and
available but are not used: this is a length identity, not a positional lookup. -/

@[simp] theorem len_listDecodeValue_mpValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (r p : V) :
    len (listDecodeValue (mpValue r p)) =
      len (listDecodeValue r) + len (listDecodeValue p) + 1 := by
  rw [listDecodeValue_mpValue]
  simp only [len_vecAppendValue, len_adjoin, len_nil, zero_add]
  exact (add_assoc _ _ _).symm

/-! ### S5: decoded MP left-prefix preservation

Every decoded line of the left input code `r` survives, at its original index,
in the decoded MP output, in an arbitrary model of `𝗜𝚺₁`.

Here `r` and `p` are internal numerical proof-sequence codes and `i` is an
internal index. `listDecodeValue r` is the outer left prefix of the decoded MP
output, so under the sole bound `i < len (listDecodeValue r)` the output's entry
at `i` is `r`'s own entry at `i`. No bound involving `p` and no bound involving
the output length is required.

What is preserved is the **numerical line code** at position `i`. The theorem
does not state or prove preservation of line justification, formula validity,
proof validity, or any leaf predicate; those belong to later results.

The theorem is deliberately **untagged**. It mirrors the conditional S2 theorem
`vecAppendValue_nth_lt`, and tagging a conditional lookup law `@[simp]` would
install a hypothesis-discharging rewrite into the simp set.

Two steps. `listDecodeValue_mpValue`, the inherited decoder/MP bridge, exposes
the decoded output as an outer `vecAppendValue` whose left operand is exactly
`listDecodeValue r`; S2 then applies directly with `hi`. These are the only
inherited theorems invoked directly by S5's proof body. S1 `len_vecAppendValue`,
S3 `vecAppendValue_nth_len_add`, and S4 `len_listDecodeValue_mpValue` are
inherited and available but not directly invoked: S5 reads a position inside the left
prefix, so it needs neither a length law nor a shifted-index law. -/

theorem listDecodeValue_mpValue_nth_r
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (r p : V) {i : V}
    (hi : i < len (listDecodeValue r)) :
    (listDecodeValue (mpValue r p)).[i] =
      (listDecodeValue r).[i] := by
  rw [listDecodeValue_mpValue]
  exact vecAppendValue_nth_lt _ _ hi

/-! ### S6: decoded MP antecedent-block preservation

Every decoded line of the antecedent proof sequence `p` survives, at its
shifted index, in the decoded MP output, in an arbitrary model of `𝗜𝚺₁`.

The decoded MP output has the structural form

    listDecodeValue r ++ᵥ (listDecodeValue p ++ᵥ [rhs(last(listDecodeValue r))])

writing `++ᵥ` for `vecAppendValue`. Reading it at the internal index
`len (listDecodeValue r) + i` first steps past the whole decoded `r` block, then
lands at position `i` of the inner append; under `i < len (listDecodeValue p)`
that position holds `p`'s own entry at `i`.

The theorem has exactly one bound, on `i` relative to the decoded `p` block.
There is no bound involving the length of `r` — the shift `len (listDecodeValue
r) + i` is unconditional, by S3 — and no separate bound involving the total
output length.

What is preserved is the **numerical line code** at that position, and nothing
more. The theorem does not state or prove preservation of line justification,
formula validity, proof validity, or any leaf predicate.

The theorem is deliberately **untagged**. Like S2 and S5 it is conditional, and
tagging a conditional lookup law `@[simp]` would install a
hypothesis-discharging rewrite into the simp set.

S6's proof body directly invokes exactly three inherited theorems. Other
inherited declarations are not separately cited by S6's source; some are
transitive dependencies of those theorems, while others are cumulative
continuity surface. No minimal dependency-closure claim is made.

  1. `listDecodeValue_mpValue` exposes the decoded output as the nested append
     shown above;
  2. `vecAppendValue_nth_len_add` (S3) removes the outer shift, unconditionally,
     leaving a read of the inner append at `i`;
  3. `vecAppendValue_nth_lt` (S2) applies to that inner append with `hi`.

S6 does not directly invoke `len_vecAppendValue` (S1),
`len_listDecodeValue_mpValue` (S4), or `listDecodeValue_mpValue_nth_r` (S5);
each remains inherited and available. -/

theorem listDecodeValue_mpValue_nth_p
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (r p : V) {i : V}
    (hi : i < len (listDecodeValue p)) :
    (listDecodeValue (mpValue r p)).[len (listDecodeValue r) + i] =
      (listDecodeValue p).[i] := by
  rw [listDecodeValue_mpValue, vecAppendValue_nth_len_add]
  exact vecAppendValue_nth_lt (listDecodeValue p) _ hi

/-! ### S7: decoded MP appended line

The line appended by the numerical MP transformation occurs at the index
immediately following the decoded `r` and `p` blocks, in an arbitrary model of
`𝗜𝚺₁`.

The decoded MP output has the structural form

    listDecodeValue r ++ᵥ (listDecodeValue p ++ᵥ [rhs(last(listDecodeValue r))])

writing `++ᵥ` for `vecAppendValue`. Reading it at the internal index

    len (listDecodeValue r) + len (listDecodeValue p)

steps past the whole decoded `r` block, then past the whole decoded `p` block,
landing on the single appended element.

The statement is **unconditional**: no hypothesis constrains `r` or `p`. Both
shifts are supplied by S3 `vecAppendValue_nth_len_add`, which is itself
unconditional, so no side condition arises.

Unlike conditional S2, S5, and S6, S7 is unconditional and strictly normalizes a
lookup in the decoded MP output — a compound `nth` application on the left, a
smaller non-`nth` term on the right — so it is marked `@[simp]`.

Proof shape. `listDecodeValue_mpValue` exposes the nested append. The first
`vecAppendValue_nth_len_add` removes the outer shift `len (listDecodeValue r) +
_`, leaving a read of the inner append at index `len (listDecodeValue p)`. The
second `vecAppendValue_nth_len_add`, instantiated at the one-element right
operand and index `(0 : V)`, is then rewritten by `add_zero` and
`nth_adjoin_zero` into exactly that read. The `simpa only` set is closed and
explicitly enumerated; it is not a broad `simp` call.

S7's proof body directly uses exactly `listDecodeValue_mpValue`,
`vecAppendValue_nth_len_add` twice, `add_zero`, and `nth_adjoin_zero`. No
minimal dependency-closure claim is made: other inherited declarations may be
transitive dependencies of those results or cumulative continuity surface. S1,
S2, S4, S5, and S6 are not directly cited here.

S7 identifies a numerical line code at the appended position. It does not prove
that this position is the output's last position, that the code equals a
separately supplied consequent `b`, or that the line is justified. -/

@[simp] theorem listDecodeValue_mpValue_nth_conclusion
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (r p : V) :
    (listDecodeValue (mpValue r p)).[
        len (listDecodeValue r) + len (listDecodeValue p)] =
      rhsValue (lastValue (listDecodeValue r)) := by
  rw [listDecodeValue_mpValue, vecAppendValue_nth_len_add]
  simpa only [add_zero, nth_adjoin_zero] using
    (vecAppendValue_nth_len_add
      (listDecodeValue p)
      (rhsValue (lastValue (listDecodeValue r)) ∷ 0)
      (0 : V))

/-! ### S8: decoded MP output final-line identity

The last line of the decoded MP output is the line the numerical MP
transformation appends, in an arbitrary model of `𝗜𝚺₁`.

Four inherited facts compose. S4 `len_listDecodeValue_mpValue` gives the decoded
output a **successor length**, `len (listDecodeValue r) + len (listDecodeValue p)
+ 1`, so the output is nonempty and its final position is that length minus one.
Foundation's `takeLast_succ_of_lt` identifies `lastValue` — defined as
`nth (takeLast v 1) 0` — with the lookup at that final position. `add_sub_self`
rewrites the position to `len (listDecodeValue r) + len (listDecodeValue p)`.
S7 `listDecodeValue_mpValue_nth_conclusion` identifies the entry there as
`rhsValue (lastValue (listDecodeValue r))`.

The public statement contains **no subtraction**. Subtraction appears only
inside the proof, introduced by `takeLast_succ_of_lt` and eliminated by the
exact successor-length equation together with `add_sub_self`. Foundation's `Sub`
at an arbitrary model is truncated rather than `Nat.sub`, so keeping it out of
the statement keeps S8 free of any truncation caveat.

The first `calc` step is deliberately isolated, and its `simpa only` rewrite set
is closed and explicitly enumerated. It must not be replaced by a top-level
`rw [lastValue]` or `simp [lastValue]`: the goal's right-hand side contains a
second, distinct `lastValue` occurrence inside
`rhsValue (lastValue (listDecodeValue r))`, and a top-level unfolding could
rewrite that occurrence too.

No new helper, definition, instance, recursion, or induction is introduced. The
induction a last-element law would otherwise need is already encapsulated in
`takeLast_succ_of_lt`, which Foundation proves by
`adjoin_ISigma1.sigma1_succ_induction`.

S8 is unconditional — no hypothesis constrains `r` or `p` — and it normalizes
`lastValue` applied to a decoded MP output into a smaller term, so it is marked
`@[simp]`, unlike the conditional lookup laws S2, S5, and S6. -/

@[simp] theorem lastValue_listDecodeValue_mpValue
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (r p : V) :
    lastValue (listDecodeValue (mpValue r p)) =
      rhsValue (lastValue (listDecodeValue r)) := by
  have hpos :
      (0 : V) < len (listDecodeValue (mpValue r p)) := by
    rw [len_listDecodeValue_mpValue]
    exact lt_succ_iff_le.mpr (Arithmetic.zero_le _)
  calc
    lastValue (listDecodeValue (mpValue r p)) =
        (listDecodeValue (mpValue r p)).[
          len (listDecodeValue (mpValue r p)) - 1] := by
      simpa only [lastValue, zero_add, nth_adjoin_zero] using
        congrArg (fun w : V => w.[0])
          (takeLast_succ_of_lt
            (i := (0 : V))
            (v := listDecodeValue (mpValue r p)) hpos)
    _ = (listDecodeValue (mpValue r p)).[
          len (listDecodeValue r) + len (listDecodeValue p)] := by
      rw [len_listDecodeValue_mpValue, add_sub_self]
    _ = rhsValue (lastValue (listDecodeValue r)) :=
      listDecodeValue_mpValue_nth_conclusion r p

/-! ### Successor-index lookup at the last value

This bridge keeps subtraction out of its public statement. The truncated
subtraction appearing in Foundation's internal-model `takeLast` law is confined
to the proof and eliminated using the supplied successor-length equation.

The theorem is conditional and therefore deliberately not a simp lemma. -/

theorem nth_eq_lastValue_of_len_eq_succ
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (v : V) {i : V}
    (hlen : len v = i + 1) :
    v.[i] = lastValue v := by
  have hpos : (0 : V) < len v := by
    rw [hlen]
    exact lt_succ_iff_le.mpr (Arithmetic.zero_le _)
  calc
    v.[i] = v.[len v - 1] := by
      rw [hlen, add_sub_self]
    _ = lastValue v := by
      symm
      simpa only [lastValue, zero_add, nth_adjoin_zero] using
        congrArg (fun w : V => w.[0])
          (takeLast_succ_of_lt
            (i := (0 : V))
            (v := v) hpos)

/-! ### S9: final entry of the decoded left block

If the decoded left block has successor length `i + 1`, then its final value is
at index `i`. S5 preserves that index in the decoded MP output. This remains a
purely positional result; later proof hypotheses are needed before the value can
serve as an MP implication witness.

The theorem is conditional and deliberately untagged. -/

theorem listDecodeValue_mpValue_nth_r_last
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (r p : V) {i : V}
    (hlen : len (listDecodeValue r) = i + 1) :
    (listDecodeValue (mpValue r p)).[i] =
      lastValue (listDecodeValue r) := by
  have hi : i < len (listDecodeValue r) := by
    rw [hlen]
    exact lt_succ_iff_le.mpr (le_refl i)
  calc
    (listDecodeValue (mpValue r p)).[i] =
        (listDecodeValue r).[i] :=
      listDecodeValue_mpValue_nth_r r p hi
    _ = lastValue (listDecodeValue r) :=
      nth_eq_lastValue_of_len_eq_succ (listDecodeValue r) hlen

/-! ### S10: final entry of the decoded right block

If `listDecodeValue p` has successor length `i + 1`, then `i` indexes its final
entry. S6 places that entry at output index `len (listDecodeValue r) + i`.
Composing the two gives S10: reading the decoded MP output at that shifted index
returns the last value of the decoded right block.

The bridge `nth_eq_lastValue_of_len_eq_succ`, introduced in B8R25 for the left
block, is reused here unchanged for the right block. That reuse is exactly what
its generic statement over an arbitrary internal Vec was written to permit.

The hypothesis is stated as the equation `len (listDecodeValue p) = i + 1`, not
as a subtraction. Foundation's `Sub` at an arbitrary model of `𝗜𝚺₁` is
truncated rather than `Nat.sub`, so an equational hypothesis keeps the public
statement free of any truncation obligation.

The result is **purely positional**. It identifies which internal value sits at
one internal index of the decoded output, and nothing further. In particular:

* it does **not** assert that `r` codes a proof;
* it does **not** assert that `p` codes a proof;
* it does **not** assert that either selected value has implication semantics;
* it does **not** assert that either selected value has antecedent semantics;
* it does **not** prove that any line of the decoded output is justified.

Each of those requires additional hypotheses that this checkpoint neither
supplies nor uses.

The theorem is conditional and is therefore deliberately untagged. -/

theorem listDecodeValue_mpValue_nth_p_last
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (r p : V) {i : V}
    (hlen : len (listDecodeValue p) = i + 1) :
    (listDecodeValue (mpValue r p)).[
        len (listDecodeValue r) + i] =
      lastValue (listDecodeValue p) := by
  have hi : i < len (listDecodeValue p) := by
    rw [hlen]
    exact lt_succ_iff_le.mpr (le_refl i)
  calc
    (listDecodeValue (mpValue r p)).[
        len (listDecodeValue r) + i] =
        (listDecodeValue p).[i] :=
      listDecodeValue_mpValue_nth_p r p hi
    _ = lastValue (listDecodeValue p) :=
      nth_eq_lastValue_of_len_eq_succ (listDecodeValue p) hlen

/-! ### R1a: `lineCheck` preservation over the unshifted decoded `r` block

At a bounded position `i < len (listDecodeValue r)`, satisfaction of the reduced
`lineCheck` body transfers from the decoded input `r` to the decoded MP output.

This is the first of U1's three logical obligations. It is a sub-obligation, not
a structural node: it is not S11, and it completes neither R1 nor U1.

The proof expands `lineCheck_iff` on both sides and then proceeds atom by atom.

* **Current-line atom.** The `nthDef` atom naming the current line's code `ci`
  is transferred by S5 `listDecodeValue_mpValue_nth_r` at index `i`, using the
  hypothesis `hi` directly.

* **Logical-axiom leaf.** Reused **unchanged**. The atom is copied verbatim from
  the input disjunct to the output disjunct; nothing classifies its extension.

* **Theory-axiom leaf.** Reused **unchanged**, for the same reason.

* **MP branch.** The same witnesses `j`, `k`, `cj`, and `ck` are retained, and
  the `impGraph` atom relating them is reused unchanged. The two earlier-line
  `nthDef` atoms are transferred by S5 at indices `j` and `k`. Those two
  applications need `j < len (listDecodeValue r)` and
  `k < len (listDecodeValue r)`, which follow from `j < i`, `k < i`, and `hi` by
  transitivity of the internal order.

S5 is therefore used at exactly the three relevant indices `i`, `j`, and `k`. No
S6–S10 theorem is required directly.

Neither standard-natural-number leaf theorem is applied. The axiom leaves remain
opaque arbitrary-model atoms, and the argument relies only on syntactic identity
of each leaf atom, not on any characterization of its nonstandard extension.

The theorem is conditional and is deliberately untagged. Its premise is the
reduced `lineCheck` body, not `proofGraph`; it does not establish
`LineJustifiedCodeNF`, a range-aware line predicate, formula validity, or that
either `r` or `p` codes a proof. -/

theorem lineCheck_listDecodeValue_mpValue_nth_r
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Th : PRTheoryPresentation)
    (r p : V) {i : V}
    (hi : i < len (listDecodeValue r))
    (hline :
      Semiformula.Evalb (M := V)
        ![listDecodeValue r, i] (lineCheck Th).val) :
    Semiformula.Evalb (M := V)
      ![listDecodeValue (mpValue r p), i]
        (lineCheck Th).val := by
  rw [lineCheck_iff] at hline ⊢
  rcases hline with ⟨ci, hci, hcase⟩
  have hci' :
      Semiformula.Evalb (M := V)
        ![ci, listDecodeValue (mpValue r p), i]
          nthDef.val := by
    simpa [listDecodeValue_mpValue_nth_r r p hi] using hci
  refine ⟨ci, hci', ?_⟩
  rcases hcase with
    hlog | hth | ⟨j, hj, k, hk, cj, hcj, ck, hck, himp⟩
  · exact Or.inl hlog
  · exact Or.inr (Or.inl hth)
  · have hjr : j < len (listDecodeValue r) :=
      Arithmetic.lt_trans _ _ _ hj hi
    have hkr : k < len (listDecodeValue r) :=
      Arithmetic.lt_trans _ _ _ hk hi
    have hcj' :
        Semiformula.Evalb (M := V)
          ![cj, listDecodeValue (mpValue r p), j]
            nthDef.val := by
      simpa [listDecodeValue_mpValue_nth_r r p hjr] using hcj
    have hck' :
        Semiformula.Evalb (M := V)
          ![ck, listDecodeValue (mpValue r p), k]
            nthDef.val := by
      simpa [listDecodeValue_mpValue_nth_r r p hkr] using hck
    exact Or.inr (Or.inr
      ⟨j, hj, k, hk, cj, hcj', ck, hck', himp⟩)

/-! ### R1b: reduced line-check preservation over the shifted decoded `p` block

R1a preserved the reduced `lineCheck` body over the unshifted decoded `r` prefix
of the decoded MP output. R1b is the complementary obligation for the second
block: a position `i` bounded by `len (listDecodeValue p)` inside the decoded
`p` block occurs in the decoded MP output at the shifted position

    len (listDecodeValue r) + i

and satisfaction of the reduced line predicate is preserved along that shift.

The proof expands `lineCheck_iff` on both the hypothesis and the goal, so the
argument is entirely at the level of the reduced body.

* **Current-line code.** The existential witness `ci` is retained unchanged. Its
  `nthDef` atom is transferred by S6, `listDecodeValue_mpValue_nth_p`, at the
  index `i`.

* **Logical-axiom leaf.** Reused **unchanged**: the leaf atom mentions only `ci`,
  which does not change.

* **Theory-axiom leaf.** Reused **unchanged**, for the same reason.

* **MP branch.** The earlier-line witnesses `j` and `k` are **replaced** by the
  shifted witnesses `len (listDecodeValue r) + j` and
  `len (listDecodeValue r) + k`. Retaining unshifted `j` and `k` in the output
  branch would be mathematically wrong: in the decoded MP output those indices
  address the decoded `r` block, not the decoded `p` block, so the reindexed
  `nthDef` atoms would not be the ones supplied by the hypothesis. The two
  strict bounds `len (listDecodeValue r) + j < len (listDecodeValue r) + i` and
  `len (listDecodeValue r) + k < len (listDecodeValue r) + i` follow from `j < i`
  and `k < i` by strict monotonicity of internal addition,
  `Arithmetic.add_lt_add`, whose orientation is right addition; `simpa [add_comm]`
  supplies the left-shifted form. The codes `cj` and `ck` and the `impGraph` atom
  relating them are retained unchanged, and their two `nthDef` atoms are
  transferred by S6 at the indices `j` and `k`, which are bounded by
  `len (listDecodeValue p)` through `j < i`, `k < i`, and `hi` by transitivity of
  the internal order.

S6 is therefore used at exactly the three relevant indices `i`, `j`, and `k`.
Neither S5 nor any S7–S10 theorem is used directly; each remains inherited and
available.

Neither standard-natural-number leaf theorem is applied. The axiom leaves remain
opaque arbitrary-model atoms, and the argument relies only on syntactic identity
of each leaf atom, not on any characterization of its nonstandard extension.

The theorem is conditional and is deliberately untagged. Its premise is the
reduced `lineCheck` body, not `proofGraph`; it does not establish
`LineJustifiedCodeNF`, a range-aware line predicate, formula validity, or that
either `r` or `p` codes a proof. Together with R1a it completes R1; it does not
complete U1. -/

theorem lineCheck_listDecodeValue_mpValue_nth_p
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Th : PRTheoryPresentation)
    (r p : V) {i : V}
    (hi : i < len (listDecodeValue p))
    (hline :
      Semiformula.Evalb (M := V)
        ![listDecodeValue p, i] (lineCheck Th).val) :
    Semiformula.Evalb (M := V)
      ![listDecodeValue (mpValue r p),
        len (listDecodeValue r) + i]
        (lineCheck Th).val := by
  rw [lineCheck_iff] at hline ⊢
  rcases hline with ⟨ci, hci, hcase⟩
  have hci' :
      Semiformula.Evalb (M := V)
        ![ci, listDecodeValue (mpValue r p),
          len (listDecodeValue r) + i]
          nthDef.val := by
    simpa [listDecodeValue_mpValue_nth_p r p hi] using hci
  refine ⟨ci, hci', ?_⟩
  rcases hcase with
    hlog | hth | ⟨j, hj, k, hk, cj, hcj, ck, hck, himp⟩
  · exact Or.inl hlog
  · exact Or.inr (Or.inl hth)
  · have hjp : j < len (listDecodeValue p) :=
      Arithmetic.lt_trans _ _ _ hj hi
    have hkp : k < len (listDecodeValue p) :=
      Arithmetic.lt_trans _ _ _ hk hi
    have hj' :
        len (listDecodeValue r) + j <
          len (listDecodeValue r) + i := by
      simpa [add_comm] using
        (Arithmetic.add_lt_add
          j i (len (listDecodeValue r)) hj)
    have hk' :
        len (listDecodeValue r) + k <
          len (listDecodeValue r) + i := by
      simpa [add_comm] using
        (Arithmetic.add_lt_add
          k i (len (listDecodeValue r)) hk)
    have hcj' :
        Semiformula.Evalb (M := V)
          ![cj, listDecodeValue (mpValue r p),
            len (listDecodeValue r) + j]
            nthDef.val := by
      simpa [listDecodeValue_mpValue_nth_p r p hjp] using hcj
    have hck' :
        Semiformula.Evalb (M := V)
          ![ck, listDecodeValue (mpValue r p),
            len (listDecodeValue r) + k]
            nthDef.val := by
      simpa [listDecodeValue_mpValue_nth_p r p hkp] using hck
    exact Or.inr (Or.inr
      ⟨len (listDecodeValue r) + j, hj',
       len (listDecodeValue r) + k, hk',
       cj, hcj', ck, hck', himp⟩)

/-! ### R2: justification of the appended decoded MP line

R1a and R1b preserve the reduced `lineCheck` body at the inherited positions of
the decoded `r` and `p` blocks. The one remaining localized obligation concerns
the single line that the internal decoded-MP construction appends, at output
index `len (listDecodeValue r) + len (listDecodeValue p)`.

The premises are a `proofGraph` premise for `r` with final code `c`, a
`proofGraph` premise for `p` with final code `a`, and `impGraph c a b`. From the
first two, `proofGraph_iff` gives nonemptiness of each decoded block and
identifies its last value, so `len (listDecodeValue r) = ir + 1` and
`len (listDecodeValue p) = ip + 1` for some `ir` and `ip`.

S7 identifies the appended entry as `rhsValue (lastValue (listDecodeValue r))`;
`hrlast`, `impGraph_iff_impValue`, and `rhsValue_impValue` reduce that entry to
`b`. S9 places the former final line of `r`, whose code is `c`, at output index
`ir`. S10 places the former final line of `p`, whose code is `a`, at output
index `len (listDecodeValue r) + ip`. Both indices are strictly below the
appended index, so the final MP disjunct of `lineCheck_iff` is discharged with
antecedent position `len (listDecodeValue r) + ip` and code `a`, implication
position `ir` and code `c`, current code `b`, and the premise `impGraph c a b`
reused unchanged.

S8 is not used here. It states the last value of the decoded MP output, which
this reduced `lineCheck` obligation does not need; S8 becomes relevant when the
output `proofGraph` is reconstructed.

This theorem establishes neither `proofGraph` for `mpValue r p` nor the bounded
partition of every output index. U1 requires both, in addition to the three
localized line obligations that R1a, R1b, and this theorem complete. -/
theorem lineCheck_listDecodeValue_mpValue_nth_conclusion
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Th : PRTheoryPresentation)
    (r p c a b : V)
    (hr :
      Semiformula.Evalb (M := V)
        ![r, c] (proofGraph Th).val)
    (hp :
      Semiformula.Evalb (M := V)
        ![p, a] (proofGraph Th).val)
    (himp :
      Semiformula.Evalb (M := V)
        ![c, a, b] impGraph.val) :
    Semiformula.Evalb (M := V)
      ![listDecodeValue (mpValue r p),
        len (listDecodeValue r) + len (listDecodeValue p)]
        (lineCheck Th).val := by
  rcases (proofGraph_iff Th r c).mp hr with
    ⟨hrne, hrlast, _⟩
  rcases (proofGraph_iff Th p a).mp hp with
    ⟨hpne, hplast, _⟩
  have hlr0 : len (listDecodeValue r) ≠ 0 := by
    intro hzero
    exact hrne (len_zero_iff_eq_nil.mp hzero)
  have hlp0 : len (listDecodeValue p) ≠ 0 := by
    intro hzero
    exact hpne (len_zero_iff_eq_nil.mp hzero)
  obtain ⟨ir, hir⟩ := nonzero_eq_succ hlr0
  obtain ⟨ip, hip⟩ := nonzero_eq_succ hlp0
  have hirlt : ir < len (listDecodeValue r) := by
    rw [hir]
    exact lt_succ_iff_le.mpr (le_refl ir)
  have hiplt : ip < len (listDecodeValue p) := by
    rw [hip]
    exact lt_succ_iff_le.mpr (le_refl ip)
  have hj :
      len (listDecodeValue r) + ip <
        len (listDecodeValue r) + len (listDecodeValue p) := by
    simpa [add_comm] using
      (Arithmetic.add_lt_add
        ip (len (listDecodeValue p))
        (len (listDecodeValue r)) hiplt)
  have hk :
      ir < len (listDecodeValue r) + len (listDecodeValue p) := by
    exact lt_of_lt_of_le hirlt (by simp)
  have hcimp : c = impValue a b :=
    (impGraph_iff_impValue c a b).mp himp
  have hconclusion :
      (listDecodeValue (mpValue r p)).[
          len (listDecodeValue r) + len (listDecodeValue p)] = b := by
    calc
      (listDecodeValue (mpValue r p)).[
          len (listDecodeValue r) + len (listDecodeValue p)] =
          rhsValue (lastValue (listDecodeValue r)) :=
        listDecodeValue_mpValue_nth_conclusion r p
      _ = rhsValue c := by rw [hrlast]
      _ = rhsValue (impValue a b) := by rw [hcimp]
      _ = b := rhsValue_impValue a b
  have hantecedent :
      (listDecodeValue (mpValue r p)).[
          len (listDecodeValue r) + ip] = a := by
    calc
      (listDecodeValue (mpValue r p)).[
          len (listDecodeValue r) + ip] =
          lastValue (listDecodeValue p) :=
        listDecodeValue_mpValue_nth_p_last r p hip
      _ = a := hplast
  have himplication :
      (listDecodeValue (mpValue r p)).[ir] = c := by
    calc
      (listDecodeValue (mpValue r p)).[ir] =
          lastValue (listDecodeValue r) :=
        listDecodeValue_mpValue_nth_r_last r p hir
      _ = c := hrlast
  have hci :
      Semiformula.Evalb (M := V)
        ![b, listDecodeValue (mpValue r p),
          len (listDecodeValue r) + len (listDecodeValue p)]
          nthDef.val := by
    simpa using hconclusion.symm
  have hcj :
      Semiformula.Evalb (M := V)
        ![a, listDecodeValue (mpValue r p),
          len (listDecodeValue r) + ip]
          nthDef.val := by
    simpa using hantecedent.symm
  have hck :
      Semiformula.Evalb (M := V)
        ![c, listDecodeValue (mpValue r p), ir]
          nthDef.val := by
    simpa using himplication.symm
  rw [lineCheck_iff]
  exact ⟨b, hci, Or.inr (Or.inr
    ⟨len (listDecodeValue r) + ip, hj,
     ir, hk,
     a, hcj,
     c, hck,
     himp⟩)⟩

/-! ### U1-partition: bounded decomposition of a decoded MP output index

R1a, R1b, and R2 discharge the three localized line obligations: preservation of
the reduced `lineCheck` body over the unshifted decoded `r` block, over the
shifted decoded `p` block, and justification of the single appended line. To
reconstruct `proofGraph` for `mpValue r p`, each of those three results must be
applied at the right index, which first requires knowing that every output index
strictly below the output length falls into one of the three corresponding
positions.

S4, `len_listDecodeValue_mpValue`, states that the decoded MP output has length
`len (listDecodeValue r) + len (listDecodeValue p) + 1`. Given
`i < len (listDecodeValue (mpValue r p))`, the order dichotomy at
`len (listDecodeValue r)` either places `i` in the left prefix or supplies,
through `le_iff_exists_add`, a `j` with `i = len (listDecodeValue r) + j`.
Additive strict-order cancellation and `lt_succ_iff_le` then bound `j` by
`len (listDecodeValue p)`, and `Arithmetic.le_def` separates
`j = len (listDecodeValue p)`, the appended index, from
`j < len (listDecodeValue p)`, a position of the shifted right block.

The equality orientations are deliberate. R1b concludes at
`len (listDecodeValue r) + i` and R2 concludes at
`len (listDecodeValue r) + len (listDecodeValue p)`, so stating the cases with
`i` on the left lets the later reconstruction rewrite an output index into
exactly the form those theorems expect.

This theorem is purely positional. It asserts neither uniqueness nor pairwise
disjointness of the three cases, and it establishes no `lineCheck` satisfaction,
no `proofGraph` closure, and no property of `r` or `p` as proof codes. -/
theorem lt_len_listDecodeValue_mpValue_cases
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (r p : V) {i : V}
    (hi : i < len (listDecodeValue (mpValue r p))) :
    i < len (listDecodeValue r) ∨
      (∃ j : V,
        j < len (listDecodeValue p) ∧
        i = len (listDecodeValue r) + j) ∨
      i = len (listDecodeValue r) + len (listDecodeValue p) := by
  rw [len_listDecodeValue_mpValue] at hi
  rcases lt_or_ge i (len (listDecodeValue r)) with hir | hri
  · exact Or.inl hir
  · rcases le_iff_exists_add.mp hri with ⟨j, hij⟩
    rw [hij] at hi
    have hjlt :
        j < len (listDecodeValue p) + 1 := by
      exact
        (add_lt_add_iff_left
          (len (listDecodeValue r))).mp (by
            simpa [add_assoc] using hi)
    have hjle : j ≤ len (listDecodeValue p) :=
      lt_succ_iff_le.mp hjlt
    rcases Arithmetic.le_def.mp hjle with hjeq | hj
    · exact Or.inr (Or.inr (by simpa [hjeq] using hij))
    · exact Or.inr (Or.inl ⟨j, hj, hij⟩)

/-! ### U1-semantic-core: `proofGraph` for the decoded MP output

Every component of the reconstruction is now available. `mpGraph_iff_mpValue`
identifies the output code `m` with `mpValue r p`. S4 states the output length as
`len (listDecodeValue r) + len (listDecodeValue p) + 1`, a successor, which
refutes a zero length and so gives nonemptiness. S8 states the output's last
value as `rhsValue (lastValue (listDecodeValue r))`; the last-value clause of the
premise for `r` rewrites that to `rhsValue c`, `impGraph_iff_impValue` replaces
`c` by `impValue a b`, and `rhsValue_impValue` reduces the result to `b`.

For the line clause, the B8R30 partition sends each bounded output index to one
of three positions, and the three localized line results discharge them: R1a for
an index of the unshifted decoded `r` prefix, R1b for a shifted index
`len (listDecodeValue r) + j`, and R2 for the appended index. The equality
orientations proved in B8R30 are exactly the ones `rw` needs at those two
positions.

`lineCheck_iff` is not expanded here. R1a, R1b, and R2 contain those arguments,
and S5, S6, S7, S9, and S10 are applied inside them rather than in this proof.

This theorem is a semantic implication in an arbitrary model of `𝗜𝚺₁`. It
defines no closed six-variable sentence, proves satisfaction of no named
sentence, and yields no derivation in `𝗜𝚺₁` or PA. Defining that sentence and
proving its validity in every model is the next checkpoint. -/
theorem proofGraph_of_mpGraph
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Th : PRTheoryPresentation)
    (p a c b r m : V)
    (hp :
      Semiformula.Evalb (M := V)
        ![p, a] (proofGraph Th).val)
    (himp :
      Semiformula.Evalb (M := V)
        ![c, a, b] impGraph.val)
    (hr :
      Semiformula.Evalb (M := V)
        ![r, c] (proofGraph Th).val)
    (hmp :
      Semiformula.Evalb (M := V)
        ![m, r, p] mpGraph.val) :
    Semiformula.Evalb (M := V)
      ![m, b] (proofGraph Th).val := by
  have hm : m = mpValue r p :=
    (mpGraph_iff_mpValue m r p).mp hmp
  rw [hm]
  rcases (proofGraph_iff Th r c).mp hr with
    ⟨_, hrlast, hrlines⟩
  rcases (proofGraph_iff Th p a).mp hp with
    ⟨_, _, hplines⟩
  rw [proofGraph_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    have hlen :
        len (listDecodeValue (mpValue r p)) = 0 :=
      len_zero_iff_eq_nil.mpr hzero
    rw [len_listDecodeValue_mpValue] at hlen
    exact Arithmetic.succ_ne_zero _ hlen
  · have hcimp : c = impValue a b :=
      (impGraph_iff_impValue c a b).mp himp
    calc
      lastValue (listDecodeValue (mpValue r p)) =
          rhsValue (lastValue (listDecodeValue r)) :=
        lastValue_listDecodeValue_mpValue r p
      _ = rhsValue c := by rw [hrlast]
      _ = rhsValue (impValue a b) := by rw [hcimp]
      _ = b := rhsValue_impValue a b
  · intro i hi
    rcases lt_len_listDecodeValue_mpValue_cases r p hi with
      hir | ⟨j, hj, hij⟩ | hiconclusion
    · exact lineCheck_listDecodeValue_mpValue_nth_r
        Th r p hir (hrlines i hir)
    · rw [hij]
      exact lineCheck_listDecodeValue_mpValue_nth_p
        Th r p hj (hplines j hj)
    · rw [hiconclusion]
      exact lineCheck_listDecodeValue_mpValue_nth_conclusion
        Th r p c a b hr hp himp

/-! ### U1: the uniform decoded-MP closure sentence and its validity

B8R31 proved the reconstruction as a statement about arbitrary elements of a
model: from `proofGraph(p,a)`, `impGraph(c,a,b)`, `proofGraph(r,c)`, and
`mpGraph(m,r,p)` it derives `proofGraph(m,b)`. U1 asks for the corresponding
**closed object-language sentence** and for its validity in every model of
`𝗜𝚺₁`.

`uniformMPClosure Th` names that sentence. Its six variables occur in the order
`p, a, c, b, r, m`, and the component graphs are the `𝚺₁` semisentences
`proofGraph Th`, `impGraph`, and `mpGraph`, substituted at the argument
positions fixed by their own definitions. The sentence is closed: it binds all
six variables and depends only on the fixed presentation `Th`.

`models_uniformMPClosure` proves that every model of `𝗜𝚺₁` satisfies it.
`models_iff` unfolds satisfaction of the universally quantified implication into
exactly the elementwise statement that `proofGraph_of_mpGraph` already gives, so
the reconstruction core is reused unchanged. This proof does not reopen
`proofGraph_iff`, does not repartition output indices, and reproves neither R1a,
R1b, R2, nor the reconstruction core.

No hierarchy classification is placed on the complete sentence. The components
are `𝚺₁` semisentences, but the sentence is not wrapped as `𝚺₁` here and no
such classification is claimed.

This checkpoint completes U1. It yields no derivation of the sentence in `𝗜𝚺₁`,
which is U2, and none in PA, which is U3. -/
noncomputable def uniformMPClosure
    (Th : PRTheoryPresentation) : ArithmeticSentence :=
  let prf : 𝚺₁.Semisentence 2 := proofGraph Th
  let imp : 𝚺₁.Semisentence 3 := impGraph
  let mp : 𝚺₁.Semisentence 3 := mpGraph
  “∀ p a c b r m,
    !prf p a ∧
    !imp c a b ∧
    !prf r c ∧
    !mp m r p →
    !prf m b”

theorem models_uniformMPClosure
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Th : PRTheoryPresentation) :
    V↓[ℒₒᵣ] ⊧ uniformMPClosure Th := by
  simpa [uniformMPClosure, models_iff] using
    (proofGraph_of_mpGraph (V := V) Th)

/-! ### U2: derivability of the uniform closure sentence in `𝗜𝚺₁`

U1 gave two things: the closed six-variable sentence `uniformMPClosure Th`, and
`models_uniformMPClosure`, which states that every model of `𝗜𝚺₁` satisfies it.
U2 converts that all-model validity into a derivation.

The conversion is general first-order completeness, not a syntactic
construction. At the pinned Foundation commit, `Arithmetic.complete` takes a
theory `T` extending `𝗘𝗤 ℒₒᵣ`, a sentence `φ`, and a proof that `φ` holds in
every model of `T`, and returns `T ⊢ φ`. Instantiating `T` at `𝗜𝚺₁` and `φ` at
`uniformMPClosure Th`, the model hypothesis is exactly
`models_uniformMPClosure`, which is therefore reused unchanged.

Nothing here re-enters the reconstruction. The sentence is not unfolded,
`models_iff` is not used, `proofGraph_iff` is not reopened, the six binders are
neither reconstructed nor reordered, and no structural obligation of U1 is
reproved. `sigma_one_completeness_iff` is not used, and no arithmetical-hierarchy
wrapper is placed on the sentence.

The result is a derivability statement, not an explicit proof object: it asserts
that a derivation exists in `𝗜𝚺₁`, and constructs no encoded proof code. The
corresponding PA derivation is U3 and is not proved here. -/
theorem provable_uniformMPClosure
    (Th : PRTheoryPresentation) :
    𝗜𝚺₁ ⊢ uniformMPClosure Th :=
  Arithmetic.complete 𝗜𝚺₁ _ fun (V : Type) _ _ ↦
    models_uniformMPClosure (V := V) Th

/-! ### U3: the same closure sentence, derived in PA

U2 gives `𝗜𝚺₁ ⊢ uniformMPClosure Th`. PA extends `𝗜𝚺₁`: at the pinned Foundation
commit, `Peano` is `𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ Set.univ`, written `𝗣𝗔`, and the
subtheory relation `𝗜𝚺₁ ⪯ 𝗣𝗔` is an active instance. `Entailment.WeakerThan.pbl`
transports a derivation along that relation, so applying it to the U2 derivation
yields the PA derivation directly.

Nothing about the sentence is touched. `uniformMPClosure Th` is left unchanged
and not unfolded, completeness is not reapplied, and no semantic or proof-graph
characterization is reopened. Instance resolution supplies the subtheory witness;
no theory argument is reconstructed by hand.

The conclusion is derivability, not a proof object: it asserts that a PA
derivation of the sentence exists, and constructs no encoded proof code.

This completes the generic structural MP-closure layer. The separate
`Arith.Feferman.Specialization` module builds the numerical specialization and
proof-transfer operations that consume this representation. -/
theorem provable_PA_uniformMPClosure
    (Th : PRTheoryPresentation) :
    𝗣𝗔 ⊢ uniformMPClosure Th :=
  Entailment.WeakerThan.pbl (provable_uniformMPClosure Th)

/-! ## An explicit logical-axiom leaf

The selected `logicalAxiomLeaf` is adequate in the standard model, but its
extension in a nonstandard model is intentionally opaque. Concrete proof
presentations can instead supply a structural logical-axiom leaf whose
nonstandard interpretation is known. The definitions below expose that one
parameter while retaining the selected theory-axiom leaf and every other part
of the checker.

This is not an additional numerical proof predicate. The standard-model theorem
requires adequacy of the supplied leaf and concludes equivalence with the same
`Proof_T`.
-/

noncomputable def lineCheckWithLogicalAxiom
    (Th : PRTheoryPresentation)
    (logAx : 𝚺₁.Semisentence 1) : 𝚺₁.Semisentence 2 :=
  let thAx : 𝚺₁.Semisentence 1 := theoryAxiomLeaf Th
  .mkSigma
    “q i.
      ∃ ci, !nthDef ci q i ∧
        (!logAx ci ∨
         !thAx ci ∨
         ∃ j < i, ∃ k < i,
           ∃ cj, !nthDef cj q j ∧
           ∃ ck, !nthDef ck q k ∧
             !impGraph ck cj ci)”

theorem lineCheckWithLogicalAxiom_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Th : PRTheoryPresentation)
    (logAx : 𝚺₁.Semisentence 1) (q i : V) :
    Semiformula.Evalb (M := V)
        ![q, i] (lineCheckWithLogicalAxiom Th logAx).val ↔
      ∃ ci : V,
        Semiformula.Evalb (M := V) ![ci, q, i] nthDef.val ∧
        (Semiformula.Evalb (M := V) ![ci] logAx.val ∨
         Semiformula.Evalb (M := V)
            ![ci] (theoryAxiomLeaf Th).val ∨
         ∃ j : V, j < i ∧
         ∃ k : V, k < i ∧
         ∃ cj : V,
           Semiformula.Evalb (M := V) ![cj, q, j] nthDef.val ∧
         ∃ ck : V,
           Semiformula.Evalb (M := V) ![ck, q, k] nthDef.val ∧
           Semiformula.Evalb (M := V) ![ck, cj, ci] impGraph.val) := by
  simp [lineCheckWithLogicalAxiom]

theorem lineCheckWithLogicalAxiom_nat_iff
    (Th : PRTheoryPresentation)
    (logAx : 𝚺₁.Semisentence 1)
    (hlog : ∀ a : ℕ,
      Semiformula.Evalb (M := ℕ) ![a] logAx.val ↔
        Th.toTheory.syn.logicalAxiom.Holds (decodeFormula a))
    (q : List ℕ) (i : ℕ) :
    (i < q.length ∧
      Semiformula.Evalb (M := ℕ)
        ![natVecOfList q, i]
          (lineCheckWithLogicalAxiom Th logAx).val) ↔
      LineJustifiedCodeNF Th.toTheory q i := by
  rw [lineCheckWithLogicalAxiom_iff, LineJustifiedCodeNF]
  constructor
  · rintro ⟨hi, ci, hci, hcase⟩
    refine ⟨hi, ?_⟩
    have hci' : ci = q.getD i 0 := (nthDef_nat_iff ci q i).mp hci
    subst hci'
    rcases hcase with hlog' | hth | ⟨j, hj, k, hk, cj, hcj, ck, hck, himp⟩
    · exact Or.inl ((hlog _).mp hlog')
    · exact Or.inr (Or.inl ((theoryAxiomLeaf_nat_iff Th _).mp hth))
    · have hcj' : cj = q.getD j 0 := (nthDef_nat_iff cj q j).mp hcj
      have hck' : ck = q.getD k 0 := (nthDef_nat_iff ck q k).mp hck
      subst hcj'
      subst hck'
      exact Or.inr (Or.inr
        ⟨j, hj, k, hk, (impGraph_nat_iff _ _ _).mp himp⟩)
  · rintro ⟨hi, hcase⟩
    refine ⟨hi, q.getD i 0, (nthDef_nat_iff _ q i).mpr rfl, ?_⟩
    rcases hcase with hlog' | hth | ⟨j, hj, k, hk, heq⟩
    · exact Or.inl ((hlog _).mpr hlog')
    · exact Or.inr (Or.inl ((theoryAxiomLeaf_nat_iff Th _).mpr hth))
    · exact Or.inr (Or.inr
        ⟨j, hj, k, hk, q.getD j 0, (nthDef_nat_iff _ q j).mpr rfl,
         q.getD k 0, (nthDef_nat_iff _ q k).mpr rfl,
         (impGraph_nat_iff _ _ _).mpr heq⟩)

noncomputable def proofGraphWithLogicalAxiom
    (Th : PRTheoryPresentation)
    (logAx : 𝚺₁.Semisentence 1) : 𝚺₁.Semisentence 2 :=
  let check : 𝚺₁.Semisentence 2 :=
    lineCheckWithLogicalAxiom Th logAx
  .mkSigma
    “p a.
      ∃ q, !listDecodeGraph q p ∧
        q ≠ 0 ∧
        ∃ l, !lenDef l q ∧
          ∃ z, !lastGraph z q ∧
            z = a ∧
            ∀ i < l, !check q i”

private theorem proofGraphWithLogicalAxiom_raw_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Th : PRTheoryPresentation)
    (logAx : 𝚺₁.Semisentence 1) (p a : V) :
    Semiformula.Evalb (M := V)
        ![p, a] (proofGraphWithLogicalAxiom Th logAx).val ↔
      ∃ q : V,
        Semiformula.Evalb (M := V) ![q, p] listDecodeGraph.val ∧
        q ≠ 0 ∧
        ∃ l : V,
          Semiformula.Evalb (M := V) ![l, q] lenDef.val ∧
          ∃ z : V,
            Semiformula.Evalb (M := V) ![z, q] lastGraph.val ∧
            z = a ∧
            ∀ i : V, i < l →
              Semiformula.Evalb (M := V) ![q, i]
                (lineCheckWithLogicalAxiom Th logAx).val := by
  simp [proofGraphWithLogicalAxiom]

theorem proofGraphWithLogicalAxiom_iff
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Th : PRTheoryPresentation)
    (logAx : 𝚺₁.Semisentence 1) (p a : V) :
    Semiformula.Evalb (M := V)
        ![p, a] (proofGraphWithLogicalAxiom Th logAx).val ↔
      listDecodeValue p ≠ 0 ∧
      lastValue (listDecodeValue p) = a ∧
      ∀ i : V, i < len (listDecodeValue p) →
        Semiformula.Evalb (M := V)
          ![listDecodeValue p, i]
            (lineCheckWithLogicalAxiom Th logAx).val := by
  rw [proofGraphWithLogicalAxiom_raw_iff]
  constructor
  · rintro ⟨q, hq, hqne, l, hl, z, hz, hza, hlines⟩
    have hq' : q = listDecodeValue p :=
      (listDecodeGraph_iff_listDecodeValue q p).mp hq
    subst hq'
    have hl' : l = len (listDecodeValue p) := by simpa using hl
    subst hl'
    have hz' : z = lastValue (listDecodeValue p) :=
      (lastGraph_iff_lastValue _ _).mp hz
    subst hz'
    exact ⟨hqne, hza, hlines⟩
  · rintro ⟨hne, hlast, hlines⟩
    exact
      ⟨listDecodeValue p, listDecodeValue_spec p, hne,
       len (listDecodeValue p), by simp,
       lastValue (listDecodeValue p),
         (lastGraph_iff_lastValue _ _).mpr rfl,
       hlast, hlines⟩

theorem proofGraphWithLogicalAxiom_nat_iff_codeProofNF
    (Th : PRTheoryPresentation)
    (logAx : 𝚺₁.Semisentence 1)
    (hlog : ∀ a : ℕ,
      Semiformula.Evalb (M := ℕ) ![a] logAx.val ↔
        Th.toTheory.syn.logicalAxiom.Holds (decodeFormula a))
    (p a : ℕ) :
    Semiformula.Evalb (M := ℕ)
        ![p, a] (proofGraphWithLogicalAxiom Th logAx).val ↔
      CodeProofNF Th.toTheory (Metamath.Feferman.listDecode p) a := by
  rw [proofGraphWithLogicalAxiom_iff, CodeProofNF, listDecodeValue_nat,
    natVecOfList_ne_zero_iff, lastValue_natVecOfList, len_natVecOfList]
  constructor
  · rintro ⟨hne, hlast, hlines⟩
    refine ⟨hne, hlast, ?_⟩
    intro i hi
    exact (lineCheckWithLogicalAxiom_nat_iff Th logAx hlog
      (Metamath.Feferman.listDecode p) i).mp ⟨hi, hlines i hi⟩
  · rintro ⟨hne, hlast, hlines⟩
    refine ⟨hne, hlast, ?_⟩
    intro i hi
    exact ((lineCheckWithLogicalAxiom_nat_iff Th logAx hlog
      (Metamath.Feferman.listDecode p) i).mpr (hlines i hi)).2

theorem proofGraphWithLogicalAxiom_nat_iff
    (Th : PRTheoryPresentation)
    (logAx : 𝚺₁.Semisentence 1)
    (hlog : ∀ a : ℕ,
      Semiformula.Evalb (M := ℕ) ![a] logAx.val ↔
        Th.toTheory.syn.logicalAxiom.Holds (decodeFormula a))
    (p a : ℕ) :
    Semiformula.Evalb (M := ℕ)
        ![p, a] (proofGraphWithLogicalAxiom Th logAx).val ↔
      Proof_T Th.toTheory p a := by
  exact (proofGraphWithLogicalAxiom_nat_iff_codeProofNF
    Th logAx hlog p a).trans
      (proof_T_iff_codeProofNF Th.toTheory p a).symm

theorem lineCheckWithLogicalAxiom_listDecodeValue_mpValue_nth_r
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Th : PRTheoryPresentation) (logAx : 𝚺₁.Semisentence 1)
    (r p : V) {i : V}
    (hi : i < len (listDecodeValue r))
    (hline : Semiformula.Evalb (M := V)
      ![listDecodeValue r, i]
        (lineCheckWithLogicalAxiom Th logAx).val) :
    Semiformula.Evalb (M := V)
      ![listDecodeValue (mpValue r p), i]
        (lineCheckWithLogicalAxiom Th logAx).val := by
  rw [lineCheckWithLogicalAxiom_iff] at hline ⊢
  rcases hline with ⟨ci, hci, hcase⟩
  have hci' : Semiformula.Evalb (M := V)
      ![ci, listDecodeValue (mpValue r p), i] nthDef.val := by
    simpa [listDecodeValue_mpValue_nth_r r p hi] using hci
  refine ⟨ci, hci', ?_⟩
  rcases hcase with
    hlog | hth | ⟨j, hj, k, hk, cj, hcj, ck, hck, himp⟩
  · exact Or.inl hlog
  · exact Or.inr (Or.inl hth)
  · have hjr : j < len (listDecodeValue r) :=
      Arithmetic.lt_trans _ _ _ hj hi
    have hkr : k < len (listDecodeValue r) :=
      Arithmetic.lt_trans _ _ _ hk hi
    have hcj' : Semiformula.Evalb (M := V)
        ![cj, listDecodeValue (mpValue r p), j] nthDef.val := by
      simpa [listDecodeValue_mpValue_nth_r r p hjr] using hcj
    have hck' : Semiformula.Evalb (M := V)
        ![ck, listDecodeValue (mpValue r p), k] nthDef.val := by
      simpa [listDecodeValue_mpValue_nth_r r p hkr] using hck
    exact Or.inr (Or.inr
      ⟨j, hj, k, hk, cj, hcj', ck, hck', himp⟩)

theorem lineCheckWithLogicalAxiom_listDecodeValue_mpValue_nth_p
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Th : PRTheoryPresentation) (logAx : 𝚺₁.Semisentence 1)
    (r p : V) {i : V}
    (hi : i < len (listDecodeValue p))
    (hline : Semiformula.Evalb (M := V)
      ![listDecodeValue p, i]
        (lineCheckWithLogicalAxiom Th logAx).val) :
    Semiformula.Evalb (M := V)
      ![listDecodeValue (mpValue r p), len (listDecodeValue r) + i]
        (lineCheckWithLogicalAxiom Th logAx).val := by
  rw [lineCheckWithLogicalAxiom_iff] at hline ⊢
  rcases hline with ⟨ci, hci, hcase⟩
  have hci' : Semiformula.Evalb (M := V)
      ![ci, listDecodeValue (mpValue r p),
        len (listDecodeValue r) + i] nthDef.val := by
    simpa [listDecodeValue_mpValue_nth_p r p hi] using hci
  refine ⟨ci, hci', ?_⟩
  rcases hcase with
    hlog | hth | ⟨j, hj, k, hk, cj, hcj, ck, hck, himp⟩
  · exact Or.inl hlog
  · exact Or.inr (Or.inl hth)
  · have hjp : j < len (listDecodeValue p) :=
      Arithmetic.lt_trans _ _ _ hj hi
    have hkp : k < len (listDecodeValue p) :=
      Arithmetic.lt_trans _ _ _ hk hi
    have hj' : len (listDecodeValue r) + j <
        len (listDecodeValue r) + i := by
      simpa [add_comm] using
        (Arithmetic.add_lt_add j i (len (listDecodeValue r)) hj)
    have hk' : len (listDecodeValue r) + k <
        len (listDecodeValue r) + i := by
      simpa [add_comm] using
        (Arithmetic.add_lt_add k i (len (listDecodeValue r)) hk)
    have hcj' : Semiformula.Evalb (M := V)
        ![cj, listDecodeValue (mpValue r p),
          len (listDecodeValue r) + j] nthDef.val := by
      simpa [listDecodeValue_mpValue_nth_p r p hjp] using hcj
    have hck' : Semiformula.Evalb (M := V)
        ![ck, listDecodeValue (mpValue r p),
          len (listDecodeValue r) + k] nthDef.val := by
      simpa [listDecodeValue_mpValue_nth_p r p hkp] using hck
    exact Or.inr (Or.inr
      ⟨len (listDecodeValue r) + j, hj',
       len (listDecodeValue r) + k, hk',
       cj, hcj', ck, hck', himp⟩)

theorem lineCheckWithLogicalAxiom_listDecodeValue_mpValue_nth_conclusion
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Th : PRTheoryPresentation) (logAx : 𝚺₁.Semisentence 1)
    (r p c a b : V)
    (hr : Semiformula.Evalb (M := V)
      ![r, c] (proofGraphWithLogicalAxiom Th logAx).val)
    (hp : Semiformula.Evalb (M := V)
      ![p, a] (proofGraphWithLogicalAxiom Th logAx).val)
    (himp : Semiformula.Evalb (M := V) ![c, a, b] impGraph.val) :
    Semiformula.Evalb (M := V)
      ![listDecodeValue (mpValue r p),
        len (listDecodeValue r) + len (listDecodeValue p)]
        (lineCheckWithLogicalAxiom Th logAx).val := by
  rcases (proofGraphWithLogicalAxiom_iff Th logAx r c).mp hr with
    ⟨hrne, hrlast, _⟩
  rcases (proofGraphWithLogicalAxiom_iff Th logAx p a).mp hp with
    ⟨hpne, hplast, _⟩
  have hlr0 : len (listDecodeValue r) ≠ 0 := by
    intro hzero
    exact hrne (len_zero_iff_eq_nil.mp hzero)
  have hlp0 : len (listDecodeValue p) ≠ 0 := by
    intro hzero
    exact hpne (len_zero_iff_eq_nil.mp hzero)
  obtain ⟨ir, hir⟩ := nonzero_eq_succ hlr0
  obtain ⟨ip, hip⟩ := nonzero_eq_succ hlp0
  have hirlt : ir < len (listDecodeValue r) := by
    rw [hir]
    exact lt_succ_iff_le.mpr (le_refl ir)
  have hiplt : ip < len (listDecodeValue p) := by
    rw [hip]
    exact lt_succ_iff_le.mpr (le_refl ip)
  have hj : len (listDecodeValue r) + ip <
      len (listDecodeValue r) + len (listDecodeValue p) := by
    simpa [add_comm] using
      (Arithmetic.add_lt_add ip (len (listDecodeValue p))
        (len (listDecodeValue r)) hiplt)
  have hk : ir < len (listDecodeValue r) + len (listDecodeValue p) :=
    lt_of_lt_of_le hirlt (by simp)
  have hcimp : c = impValue a b :=
    (impGraph_iff_impValue c a b).mp himp
  have hconclusion :
      (listDecodeValue (mpValue r p)).[
        len (listDecodeValue r) + len (listDecodeValue p)] = b := by
    calc
      _ = rhsValue (lastValue (listDecodeValue r)) :=
        listDecodeValue_mpValue_nth_conclusion r p
      _ = rhsValue c := by rw [hrlast]
      _ = rhsValue (impValue a b) := by rw [hcimp]
      _ = b := rhsValue_impValue a b
  have hantecedent :
      (listDecodeValue (mpValue r p)).[
        len (listDecodeValue r) + ip] = a := by
    calc
      _ = lastValue (listDecodeValue p) :=
        listDecodeValue_mpValue_nth_p_last r p hip
      _ = a := hplast
  have himplication :
      (listDecodeValue (mpValue r p)).[ir] = c := by
    calc
      _ = lastValue (listDecodeValue r) :=
        listDecodeValue_mpValue_nth_r_last r p hir
      _ = c := hrlast
  have hci : Semiformula.Evalb (M := V)
      ![b, listDecodeValue (mpValue r p),
        len (listDecodeValue r) + len (listDecodeValue p)] nthDef.val := by
    simpa using hconclusion.symm
  have hcj : Semiformula.Evalb (M := V)
      ![a, listDecodeValue (mpValue r p),
        len (listDecodeValue r) + ip] nthDef.val := by
    simpa using hantecedent.symm
  have hck : Semiformula.Evalb (M := V)
      ![c, listDecodeValue (mpValue r p), ir] nthDef.val := by
    simpa using himplication.symm
  rw [lineCheckWithLogicalAxiom_iff]
  exact ⟨b, hci, Or.inr (Or.inr
    ⟨len (listDecodeValue r) + ip, hj,
     ir, hk, a, hcj, c, hck, himp⟩)⟩

theorem proofGraphWithLogicalAxiom_of_mpGraph
    {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Th : PRTheoryPresentation) (logAx : 𝚺₁.Semisentence 1)
    (p a c b r m : V)
    (hp : Semiformula.Evalb (M := V)
      ![p, a] (proofGraphWithLogicalAxiom Th logAx).val)
    (himp : Semiformula.Evalb (M := V) ![c, a, b] impGraph.val)
    (hr : Semiformula.Evalb (M := V)
      ![r, c] (proofGraphWithLogicalAxiom Th logAx).val)
    (hmp : Semiformula.Evalb (M := V) ![m, r, p] mpGraph.val) :
    Semiformula.Evalb (M := V)
      ![m, b] (proofGraphWithLogicalAxiom Th logAx).val := by
  have hm : m = mpValue r p := (mpGraph_iff_mpValue m r p).mp hmp
  rw [hm]
  rcases (proofGraphWithLogicalAxiom_iff Th logAx r c).mp hr with
    ⟨_, hrlast, hrlines⟩
  rcases (proofGraphWithLogicalAxiom_iff Th logAx p a).mp hp with
    ⟨_, _, hplines⟩
  rw [proofGraphWithLogicalAxiom_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    have hlen : len (listDecodeValue (mpValue r p)) = 0 :=
      len_zero_iff_eq_nil.mpr hzero
    rw [len_listDecodeValue_mpValue] at hlen
    exact Arithmetic.succ_ne_zero _ hlen
  · have hcimp : c = impValue a b :=
      (impGraph_iff_impValue c a b).mp himp
    calc
      lastValue (listDecodeValue (mpValue r p)) =
          rhsValue (lastValue (listDecodeValue r)) :=
        lastValue_listDecodeValue_mpValue r p
      _ = rhsValue c := by rw [hrlast]
      _ = rhsValue (impValue a b) := by rw [hcimp]
      _ = b := rhsValue_impValue a b
  · intro i hi
    rcases lt_len_listDecodeValue_mpValue_cases r p hi with
      hir | ⟨j, hj, hij⟩ | hiconclusion
    · exact lineCheckWithLogicalAxiom_listDecodeValue_mpValue_nth_r
        Th logAx r p hir (hrlines i hir)
    · rw [hij]
      exact lineCheckWithLogicalAxiom_listDecodeValue_mpValue_nth_p
        Th logAx r p hj (hplines j hj)
    · rw [hiconclusion]
      exact lineCheckWithLogicalAxiom_listDecodeValue_mpValue_nth_conclusion
        Th logAx r p c a b hr hp himp

end Arith.Feferman.Structural
