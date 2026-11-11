/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerBinaryCore
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # Bounded positive series in the effective cut reduction

These are ordinary real-analysis lemmas. Actual bad-box distances and their
numerical approximation algorithms must be supplied by their constructions;
no unanimity comparison or realizer is assumed in this module.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace CategoricalEssentialIncompleteness.V46.Miller.Cut.Series

def weight (j : ℕ) : ℝ := 1/2/(2:ℝ)^j

theorem weight_pos (j : ℕ) : 0<weight j := by unfold weight; positivity

theorem weight_nonneg (j : ℕ) : 0≤weight j := (weight_pos j).le

theorem weight_eq (j : ℕ) : weight j=((2:ℝ)^(j+1))⁻¹ := by
  simp only [weight,pow_succ]
  field_simp

theorem weight_summable : Summable weight := summable_geometric_two' 1

theorem weight_tsum : (∑' j,weight j)=1 := tsum_geometric_two' 1

theorem weight_add (j N : ℕ) : weight (j+N)=weight j*((2:ℝ)^N)⁻¹ := by
  simp only [weight,pow_add]
  field_simp

theorem weight_tail (N : ℕ) : (∑' j,weight (j+N))=((2:ℝ)^N)⁻¹ := by
  simp_rw [weight_add]
  rw [tsum_mul_right,weight_tsum,one_mul]

variable {α : Type*}

def value (δ : ℕ → α → ℝ) (z : α) : ℝ := ∑' j,weight j*δ j z

theorem value_summable (δ : ℕ → α → ℝ)
    (hδ : ∀ j z,0≤δ j z ∧ δ j z≤1) (z : α) :
    Summable (fun j => weight j*δ j z) :=
  Summable.of_nonneg_of_le
    (fun j => mul_nonneg (weight_nonneg j) (hδ j z).1)
    (fun j => mul_le_of_le_one_right (weight_nonneg j) (hδ j z).2)
    weight_summable

theorem value_nonneg (δ : ℕ → α → ℝ)
    (hδ : ∀ j z,0≤δ j z ∧ δ j z≤1) (z : α) : 0≤value δ z :=
  tsum_nonneg (fun j => mul_nonneg (weight_nonneg j) (hδ j z).1)

theorem value_le_one (δ : ℕ → α → ℝ)
    (hδ : ∀ j z,0≤δ j z ∧ δ j z≤1) (z : α) : value δ z≤1 := by
  calc
    value δ z ≤ ∑' j,weight j :=
      Summable.tsum_mono (value_summable δ hδ z) weight_summable
        (fun j => mul_le_of_le_one_right (weight_nonneg j) (hδ j z).2)
    _ = 1 := weight_tsum

theorem value_pos_iff (δ : ℕ → α → ℝ)
    (hδ : ∀ j z,0≤δ j z ∧ δ j z≤1) (z : α) :
    0<value δ z ↔ ∃ j,0<δ j z := by
  constructor
  · intro hv
    by_contra h
    have hz : ∀ j,δ j z=0 := by
      intro j
      exact le_antisymm (le_of_not_gt (fun hj => h ⟨j,hj⟩)) (hδ j z).1
    have he : value δ z=0 := by simp [value,hz]
    linarith
  · rintro ⟨j,hj⟩
    exact (mul_pos (weight_pos j) hj).trans_le
      ((value_summable δ hδ z).le_tsum j
        (fun k _ => mul_nonneg (weight_nonneg k) (hδ k z).1))

theorem value_continuous [TopologicalSpace α] (δ : ℕ → α → ℝ)
    (hδ : ∀ j z,0≤δ j z ∧ δ j z≤1) (hc : ∀ j,Continuous (δ j)) :
    Continuous (value δ) := by
  apply continuous_tsum (u := weight)
  · intro j
    exact continuous_const.mul (hc j)
  · exact weight_summable
  · intro j z
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (weight_nonneg j) (hδ j z).1)]
    exact mul_le_of_le_one_right (weight_nonneg j) (hδ j z).2

def partialValue (δ : ℕ → α → ℝ) (N : ℕ) (z : α) : ℝ :=
  ∑ j ∈ Finset.range N,weight j*δ j z

theorem tail_le (δ : ℕ → α → ℝ)
    (hδ : ∀ j z,0≤δ j z ∧ δ j z≤1) (N : ℕ) (z : α) :
    (∑' j,weight (j+N)*δ (j+N) z) ≤ ((2:ℝ)^N)⁻¹ := by
  have hs : Summable (fun j => weight (j+N)*δ (j+N) z) :=
    (summable_nat_add_iff N).2 (value_summable δ hδ z)
  have hw : Summable (fun j => weight (j+N)) :=
    (summable_nat_add_iff N).2 weight_summable
  calc
    (∑' j,weight (j+N)*δ (j+N) z) ≤ ∑' j,weight (j+N) :=
      Summable.tsum_mono hs hw
        (fun j => mul_le_of_le_one_right (weight_nonneg (j+N)) (hδ (j+N) z).2)
    _ = ((2:ℝ)^N)⁻¹ := weight_tail N

theorem partial_error (δ : ℕ → α → ℝ)
    (hδ : ∀ j z,0≤δ j z ∧ δ j z≤1) (N : ℕ) (z : α) :
    |value δ z-partialValue δ N z| ≤ ((2:ℝ)^N)⁻¹ := by
  have he := (value_summable δ hδ z).sum_add_tsum_nat_add N
  change |(∑' j,weight j*δ j z)-(∑ j ∈ Finset.range N,weight j*δ j z)| ≤ _
  rw [← he,add_sub_cancel_left]
  rw [abs_of_nonneg (tsum_nonneg (fun j =>
    mul_nonneg (weight_nonneg (j+N)) (hδ (j+N) z).1))]
  exact tail_le δ hδ N z

theorem weight_partial_le_one (N : ℕ) : (∑ j ∈ Finset.range N,weight j)≤1 := by
  calc
    (∑ j ∈ Finset.range N,weight j) ≤ ∑' j,weight j :=
      weight_summable.sum_le_tsum _ (fun j _ => weight_nonneg j)
    _ = 1 := weight_tsum

/-- Approximating each of finitely many terms by epsilon changes their
weighted sum by at most epsilon, independently of the truncation length. -/
theorem partial_approximation_error (δ : ℕ → α → ℝ) (N : ℕ) (z : α)
    (b : ℕ → ℝ) (ε : ℝ) (hε : 0≤ε)
    (hb : ∀ j<N,|δ j z-b j|≤ε) :
    |partialValue δ N z-(∑ j ∈ Finset.range N,weight j*b j)|≤ε := by
  change |(∑ j ∈ Finset.range N,weight j*δ j z)-
    (∑ j ∈ Finset.range N,weight j*b j)|≤ε
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ j ∈ Finset.range N,(weight j*δ j z-weight j*b j)| ≤
        ∑ j ∈ Finset.range N,|weight j*δ j z-weight j*b j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N,weight j*ε := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← mul_sub,abs_mul,abs_of_nonneg (weight_nonneg j)]
      exact mul_le_mul_of_nonneg_left (hb j (Finset.mem_range.mp hj)) (weight_nonneg j)
    _ = (∑ j ∈ Finset.range N,weight j)*ε := by rw [Finset.sum_mul]
    _ ≤ 1*ε := mul_le_mul_of_nonneg_right (weight_partial_le_one N) hε
    _ = ε := one_mul ε

theorem full_approximation_error (δ : ℕ → α → ℝ)
    (hδ : ∀ j z,0≤δ j z ∧ δ j z≤1) (N : ℕ) (z : α)
    (b : ℕ → ℝ) (ε : ℝ) (hε : 0≤ε)
    (hb : ∀ j<N,|δ j z-b j|≤ε) :
    |value δ z-(∑ j ∈ Finset.range N,weight j*b j)|≤((2:ℝ)^N)⁻¹+ε := by
  calc
    |value δ z-(∑ j ∈ Finset.range N,weight j*b j)| ≤
        |value δ z-partialValue δ N z|+
          |partialValue δ N z-(∑ j ∈ Finset.range N,weight j*b j)| := abs_sub_le _ _ _
    _ ≤ ((2:ℝ)^N)⁻¹+ε := add_le_add (partial_error δ hδ N z)
      (partial_approximation_error δ N z b ε hε hb)

def separating (δ0 δ1 : ℕ → α → ℝ) (z : α) : ℝ :=
  1/2+(value δ1 z-value δ0 z)/4

theorem separating_bounds (δ0 δ1 : ℕ → α → ℝ)
    (h0 : ∀ j z,0≤δ0 j z ∧ δ0 j z≤1)
    (h1 : ∀ j z,0≤δ1 j z ∧ δ1 j z≤1) (z : α) :
    1/4≤separating δ0 δ1 z ∧ separating δ0 δ1 z≤3/4 := by
  have h0n := value_nonneg δ0 h0 z
  have h0l := value_le_one δ0 h0 z
  have h1n := value_nonneg δ1 h1 z
  have h1l := value_le_one δ1 h1 z
  unfold separating
  constructor <;> linarith

theorem separating_lt_half (δ0 δ1 : ℕ → α → ℝ)
    (h0 : ∀ j z,0≤δ0 j z ∧ δ0 j z≤1)
    (h1 : ∀ j z,0≤δ1 j z ∧ δ1 j z≤1)
    (hd : ∀ z,¬(0<value δ0 z ∧ 0<value δ1 z)) (z : α) :
    separating δ0 δ1 z<1/2 ↔ ∃ j,0<δ0 j z := by
  rw [← value_pos_iff δ0 h0 z]
  have h0n := value_nonneg δ0 h0 z
  have h1n := value_nonneg δ1 h1 z
  constructor
  · intro h
    unfold separating at h
    linarith
  · intro h
    have hz : value δ1 z=0 :=
      le_antisymm (le_of_not_gt (fun h1p => hd z ⟨h,h1p⟩)) h1n
    unfold separating
    rw [hz]
    linarith

theorem separating_gt_half (δ0 δ1 : ℕ → α → ℝ)
    (h0 : ∀ j z,0≤δ0 j z ∧ δ0 j z≤1)
    (h1 : ∀ j z,0≤δ1 j z ∧ δ1 j z≤1)
    (hd : ∀ z,¬(0<value δ0 z ∧ 0<value δ1 z)) (z : α) :
    1/2<separating δ0 δ1 z ↔ ∃ j,0<δ1 j z := by
  rw [← value_pos_iff δ1 h1 z]
  have h0n := value_nonneg δ0 h0 z
  have h1n := value_nonneg δ1 h1 z
  constructor
  · intro h
    unfold separating at h
    linarith
  · intro h
    have hz : value δ0 z=0 :=
      le_antisymm (le_of_not_gt (fun h0p => hd z ⟨h0p,h⟩)) h0n
    unfold separating
    rw [hz]
    linarith

end CategoricalEssentialIncompleteness.V46.Miller.Cut.Series
