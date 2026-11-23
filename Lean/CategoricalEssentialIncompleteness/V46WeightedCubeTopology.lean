/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutBoxDistance
public import Mathlib.Topology.MetricSpace.Defs

/-! # The weighted metric induces the product topology on the Hilbert cube -/

@[expose] public section

noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller.Cut.Distance

theorem coordinate_bounds (n : ℕ) (z w : Point) :
    0 ≤ |(z n : ℝ) - w n| ∧ |(z n : ℝ) - w n| ≤ 1 := by
  have hz := (z n).property
  have hw := (w n).property
  exact ⟨abs_nonneg _, abs_le.mpr ⟨by linarith [hz.1, hw.2], by linarith [hz.2, hw.1]⟩⟩

theorem continuous_productDistance (z : Point) : Continuous (productDistance z) := by
  change Continuous (Series.value (fun n (w : Point) => |(z n : ℝ) - (w n : ℝ)|))
  apply Series.value_continuous
  · exact fun n w => coordinate_bounds n z w
  · intro n
    fun_prop

theorem positive_distance {z w : Point} (h : z ≠ w) : 0 < productDistance z w := by
  apply (Series.value_pos_iff (fun n w => |(z n : ℝ) - w n|)
    (fun n w => coordinate_bounds n z w) w).mpr
  by_contra! h₀
  apply h
  funext n
  apply Subtype.ext
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (h₀ n) (abs_nonneg _)))

/-- The distance from any point in an open set to its closed complement has a
positive minimum when that complement is nonempty. -/
theorem isOpen_iff_productDistance (s : Set Point) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, productDistance x y < ε → y ∈ s := by
  classical
  constructor
  · intro hs x hx
    by_cases hn : (sᶜ).Nonempty
    · obtain ⟨y, hy, hm⟩ :=
        hs.isClosed_compl.isCompact.exists_isMinOn hn (continuous_productDistance x).continuousOn
      refine ⟨productDistance x y, positive_distance (fun h => hy (h ▸ hx)), ?_⟩
      intro w hw
      by_contra h
      exact (not_lt_of_ge (hm h)) hw
    · exact ⟨1, zero_lt_one, fun y _ => by by_contra h; exact hn ⟨y, h⟩⟩
  · intro h
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨ε, hε, hsub⟩ := h x hx
    exact Filter.mem_of_superset ((isOpen_lt (continuous_productDistance x) continuous_const).mem_nhds
      (show productDistance x x < ε by simpa [productDistance] using hε)) (fun y hy => hsub y hy)

set_option maxHeartbeats 800000 in
/-- Its topology is definitionally the product topology of `Point`. -/
@[instance_reducible] def weightedMetric : MetricSpace Point := MetricSpace.ofDistTopology productDistance
  (fun x => by simp [productDistance])
  (fun x y => by unfold productDistance
                 exact tsum_congr fun n => congrArg (Series.weight n * ·) (abs_sub_comm (x n : ℝ) (y n : ℝ)))
  (fun x y z => by
    let δ (a b : Point) (n : ℕ) : ℝ := Series.weight n * |(a n : ℝ) - b n|
    have summable (a b : Point) : Summable (δ a b) :=
      Series.value_summable (fun n (w : Point) => |(a n : ℝ) - (w n : ℝ)|) (fun n w => coordinate_bounds n a w) b
    change (∑' n, δ x z n) ≤ (∑' n, δ x y n) + ∑' n, δ y z n
    rw [← (summable x y).tsum_add (summable y z)]
    exact (summable x z).tsum_mono ((summable x y).add (summable y z))
      (fun n => by simpa [δ, mul_add] using
        mul_le_mul_of_nonneg_left (abs_sub_le (x n : ℝ) (y n) (z n)) (Series.weight_nonneg n)))
  isOpen_iff_productDistance
  (fun _ _ h => Classical.byContradiction fun ne => (positive_distance ne).ne' h)

end CategoricalEssentialIncompleteness.V46.Miller.Cut.Distance
