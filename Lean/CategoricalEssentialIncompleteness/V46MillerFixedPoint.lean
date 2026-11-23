/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerFixedPointIntervals
import CategoricalEssentialIncompleteness.V46MillerFixedPointKakutani

/-! # Existence of a Miller sequence

The coordinate intervals have closed graphs on the Hilbert cube. Kakutani's
theorem gives simultaneous membership in any initial finite set of coordinates.
Compactness supplies a point satisfying every coordinate condition.
-/

@[expose] public section
noncomputable section

open Set
namespace CategoricalEssentialIncompleteness.V46.Miller

private abbrev Cube (m : ℕ) := Set.Icc (0 : Fin m → ℝ) 1

private def extendByZero {m : ℕ} (x : Cube m) (d : ℕ) : UnitInterval :=
  if h : d < m then ⟨x.1 ⟨d, h⟩, x.2.1 ⟨d, h⟩, x.2.2 ⟨d, h⟩⟩ else 0

private theorem continuous_extendByZero (m : ℕ) :
    Continuous (extendByZero : Cube m → Point) := by
  apply continuous_pi
  intro d
  by_cases hd : d < m
  · simp only [extendByZero, dite_eq_left hd]
    exact ((continuous_apply (⟨d, hd⟩ : Fin m)).comp continuous_subtype_val).subtype_mk _
  · simp only [extendByZero, dite_eq_right hd]
    exact continuous_const

private theorem finite_coordinate_fixedPoint (J : ℕ → Point → Set UnitInterval)
    (hg : ∀ d, IsClosed {z : Point × UnitInterval | z.2 ∈ J d z.1})
    (hb : ∀ d a, ∃ l u : UnitInterval, l ≤ u ∧ J d a = Icc l u) (m : ℕ) :
    ∃ a : Point, ∀ d < m, a d ∈ J d a := by
  let R (d : ℕ) (a : Point) : Set ℝ := Subtype.val '' J d a
  have hR (d : ℕ) : IsClosed {z : Point × ℝ | z.2 ∈ R d z.1} := by
    let f : Point × UnitInterval → Point × ℝ := fun z => (z.1, z.2.val)
    have he : {z : Point × ℝ | z.2 ∈ R d z.1} =
        f '' {z : Point × UnitInterval | z.2 ∈ J d z.1} := by
      ext ⟨a, x⟩
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨(a, v), hv, rfl⟩
      · rintro ⟨⟨b, v⟩, hv, eq⟩
        cases eq
        exact ⟨v, hv, rfl⟩
    rw [he]
    exact ((hg d).isCompact.image
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).isClosed
  let F (x : Cube m) : Set (Fin m → ℝ) := {v | ∀ i : Fin m, v i ∈ R i (extendByZero x)}
  have hF : FixedPoint.closedGraph F := by
    have he : {z : Cube m × (Fin m → ℝ) | z.2 ∈ F z.1} =
        ⋂ i : Fin m, {z : Cube m × (Fin m → ℝ) | z.2 i ∈ R i (extendByZero z.1)} := by
      ext z
      simp [F]
    unfold FixedPoint.closedGraph
    rw [he]
    apply isClosed_iInter
    intro i
    exact (hR i).preimage (f := fun z : Cube m × (Fin m → ℝ) => (extendByZero z.1, z.2 i))
      (((continuous_extendByZero m).comp continuous_fst).prodMk
        ((continuous_apply i).comp continuous_snd))
  have hvals (x : Cube m) :
      F x ⊆ (Cube m : Set (Fin m → ℝ)) ∧ Convex ℝ (F x) ∧ (F x).Nonempty := by
    choose l u hlu hj using fun i : Fin m => hb i (extendByZero x)
    let low (i : Fin m) : ℝ := l i
    let high (i : Fin m) : ℝ := u i
    have he : F x = Icc low high := by
      ext v
      constructor
      · intro hv
        have heach (i : Fin m) : low i ≤ v i ∧ v i ≤ high i := by
          obtain ⟨y, hy, eq⟩ := hv i
          rw [hj i] at hy
          exact eq ▸ hy
        exact ⟨fun i => (heach i).1, fun i => (heach i).2⟩
      · rintro ⟨hl, hu⟩ i
        have hh : v i ∈ Icc (0 : ℝ) 1 :=
          ⟨(l i).2.1.trans (hl i), (hu i).trans (u i).2.2⟩
        refine ⟨⟨v i, hh⟩, ?_, rfl⟩
        rw [hj i]
        exact ⟨hl i, hu i⟩
    rw [he]
    refine ⟨?_, convex_Icc _ _, low, le_rfl, fun i => hlu i⟩
    rintro v ⟨hl, hu⟩
    exact ⟨fun i => (l i).2.1.trans (hl i), fun i => (hu i).trans (u i).2.2⟩
  have hne : (Cube m : Set (Fin m → ℝ)).Nonempty :=
    ⟨0, le_rfl, fun _ => zero_le_one⟩
  obtain ⟨x, hx⟩ := FixedPoint.kakutani_fixed_point (Cube m) (convex_Icc _ _)
    isCompact_Icc hne F hF hvals
  refine ⟨extendByZero x, fun d hd => ?_⟩
  obtain ⟨v, hv, heq⟩ := hx ⟨d, hd⟩
  have eq : extendByZero x d = v := Subtype.ext (by simpa [extendByZero, hd] using heq.symm)
  exact eq ▸ hv

/-- Closed graphs with nonempty closed interval fibers have a common coordinate
fixed point in the countable product of unit intervals. -/
theorem exists_coordinate_fixedPoint (J : ℕ → Point → Set UnitInterval)
    (hg : ∀ d, IsClosed {z : Point × UnitInterval | z.2 ∈ J d z.1})
    (hb : ∀ d a, ∃ l u : UnitInterval, l ≤ u ∧ J d a = Icc l u) :
    ∃ a : Point, ∀ d, a d ∈ J d a := by
  let D (m : ℕ) : Set Point := {a | ∀ d < m, a d ∈ J d a}
  have hd (m : ℕ) : IsClosed (D m) := by
    have he : D m = ⋂ i : Fin m, {a : Point | a i ∈ J i a} := by
      ext a
      simp only [D, mem_ofPred_eq, mem_iInter, Fin.forall_iff]
    rw [he]
    exact isClosed_iInter fun i => (hg i).preimage (continuous_id.prodMk (continuous_apply i.val))
  have hn (m : ℕ) : (D m).Nonempty := finite_coordinate_fixedPoint J hg hb m
  have hs (m : ℕ) : D (m+1) ⊆ D m := fun _ h d hd => h d (Nat.lt_succ_of_lt hd)
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed D
    hs hn (hd 0).isCompact hd
  exact ⟨a, fun d => mem_iInter.mp ha (d+1) d (Nat.lt_succ_self d)⟩

/-- Miller's sequence existence theorem for the oracle programs, rational
enumeration and binary representation map of Section 9. -/
theorem exists_isMiller : ∃ a : Point, IsMiller a := by
  obtain ⟨a, ha⟩ := exists_coordinate_fixedPoint coordinateInterval
    coordinateInterval_graph_closed coordinateInterval_box
  exact ⟨a, isMiller_of_coordinate_mem ha⟩

end CategoricalEssentialIncompleteness.V46.Miller
