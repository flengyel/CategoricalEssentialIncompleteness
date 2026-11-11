/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutSeries


/-! # Statement checks in `V46MillerCutSeriesChecks` -/

@[expose] public section
open scoped BigOperators
namespace CategoricalEssentialIncompleteness.V46.Miller.Cut.Series.Checks
example : Summable weight := weight_summable
example : (∑' j,weight j)=1 := weight_tsum
example {α : Type*} (δ : ℕ → α → ℝ) (hδ : ∀ j z,0≤δ j z ∧ δ j z≤1) (z : α) :
    0<value δ z ↔ ∃ j,0<δ j z := value_pos_iff δ hδ z
example {α : Type*} (δ : ℕ → α → ℝ) (hδ : ∀ j z,0≤δ j z ∧ δ j z≤1) (N : ℕ) (z : α) :
    |value δ z-partialValue δ N z|≤((2:ℝ)^N)⁻¹ := partial_error δ hδ N z
example {α : Type*} [TopologicalSpace α] (δ : ℕ → α → ℝ)
    (hδ : ∀ j z,0≤δ j z ∧ δ j z≤1) (hc : ∀ j,Continuous (δ j)) :
    Continuous (value δ) := value_continuous δ hδ hc
example {α : Type*} (δ : ℕ → α → ℝ) (hδ : ∀ j z,0≤δ j z ∧ δ j z≤1)
    (N : ℕ) (z : α) (b : ℕ → ℝ) (ε : ℝ) (hε : 0≤ε) (hb : ∀ j<N,|δ j z-b j|≤ε) :
    |value δ z-(∑ j ∈ Finset.range N,weight j*b j)|≤((2:ℝ)^N)⁻¹+ε :=
  full_approximation_error δ hδ N z b ε hε hb
end CategoricalEssentialIncompleteness.V46.Miller.Cut.Series.Checks
