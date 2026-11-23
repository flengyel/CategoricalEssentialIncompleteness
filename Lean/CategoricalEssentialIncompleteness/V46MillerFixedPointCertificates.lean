/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRealComputation

/-! # Intervals determined by finite oracle computations

For a fixed program, a finite halting computation restricts the possible
values of the real it computes. Along a binary name retain a restriction
when it has nonempty intersection with the preceding restrictions.
-/

@[expose] public section
noncomputable section

open Set Filter Topology
namespace CategoricalEssentialIncompleteness.V46.Miller
open OracleProgram

abbrev UnitInterval := Set.Icc (0 : ℝ) 1

private abbrev Certificate := ℕ × ℕ × Word

private def certificate (n : ℕ) : Certificate :=
  (Encodable.decode (α := Certificate) n).getD (0, 0, [])

private theorem certificate_encode (t : Certificate) :
    certificate (Encodable.encode t) = t := by
  simp [certificate]

private def approximationBand (k i : ℕ) : Set UnitInterval :=
  {x | |(Rationals.q i : ℝ) - (x : ℝ)| ≤ ((2 : ℝ) ^ k)⁻¹}

private theorem band_closed (k i : ℕ) : IsClosed (approximationBand k i) :=
  isClosed_le (continuous_const.sub continuous_subtype_val).abs continuous_const

private def applies (d : ℕ) (t : Certificate) (p : Bits) : Prop :=
  HaltingCylinder (((Denumerable.ofNat Code d, t.1), t.2.1), t.2.2) ∧ p ∈ cylinder t.2.2

private theorem applies_near (d : ℕ) (t : Certificate) (p : Bits) :
    ∀ᶠ q in 𝓝 p, applies d t q ↔ applies d t p := by
  by_cases hp : p ∈ cylinder t.2.2
  · filter_upwards [(cylinder_isOpen t.2.2).mem_nhds hp] with q hq
    simp [applies, hp, hq]
  · filter_upwards [(cylinder_isClosed t.2.2).isOpen_compl.mem_nhds hp] with q hq
    have hn : q ∉ cylinder t.2.2 := hq
    simp [applies, hp, hn]

private noncomputable def refineBand (d : ℕ) (t : Certificate) (p : Bits)
    (s : Set UnitInterval) : Set UnitInterval := by
  classical
  exact if applies d t p ∧ (s ∩ approximationBand t.1 t.2.1).Nonempty then
    s ∩ approximationBand t.1 t.2.1 else s

private def stage (d : ℕ) (p : Bits) : ℕ → Set UnitInterval
  | 0 => univ
  | n+1 => refineBand d (certificate n) p (stage d p n)

private theorem stage_decreases (d : ℕ) (p : Bits) (n : ℕ) :
    stage d p (n+1) ⊆ stage d p n := by
  classical
  simp only [stage, refineBand]
  split
  · exact inter_subset_left
  · exact Subset.rfl

private theorem stage_nonempty (d : ℕ) (p : Bits) (n : ℕ) : (stage d p n).Nonempty := by
  classical
  induction n with
  | zero => exact univ_nonempty
  | succ n ih =>
    simp only [stage, refineBand]
    split
    next h => exact h.2
    next => exact ih

private theorem stage_closed (d : ℕ) (p : Bits) (n : ℕ) : IsClosed (stage d p n) := by
  classical
  induction n with
  | zero => exact isClosed_univ
  | succ n ih =>
    simp only [stage, refineBand]
    split
    · exact ih.inter (band_closed _ _)
    · exact ih

private theorem stage_near (d n : ℕ) (p : Bits) :
    ∀ᶠ q in 𝓝 p, stage d q n = stage d p n := by
  classical
  induction n with
  | zero => exact Eventually.of_forall fun _ => rfl
  | succ n ih =>
    filter_upwards [ih, applies_near d (certificate n) p] with q he ha
    simp only [stage, refineBand, he, ha]

private theorem stage_graph_closed (d n : ℕ) :
    IsClosed {z : Bits × UnitInterval | z.2 ∈ stage d z.1 n} := by
  apply isOpen_compl_iff.mp
  refine isOpen_iff_mem_nhds.mpr ?_
  rintro ⟨p, x⟩ hx
  have h : x ∈ (stage d p n)ᶜ := hx
  have hxo : ∀ᶠ y in 𝓝 x, y ∉ stage d p n :=
    (stage_closed d p n).isOpen_compl.mem_nhds h
  filter_upwards [(stage_near d n p).prod_inl_nhds x, hxo.prod_inr_nhds p] with z he hz
  change z.2 ∉ stage d z.1 n
  rwa [he]

private theorem stage_between (d : ℕ) (p : Bits) {x l u : UnitInterval}
    (hlx : l ≤ x) (hxu : x ≤ u) (n : ℕ) :
    l ∈ stage d p n → u ∈ stage d p n → x ∈ stage d p n := by
  classical
  induction n with
  | zero => exact fun _ _ => trivial
  | succ n ih =>
    simp only [stage, refineBand]
    split
    · rintro ⟨hl, hb⟩ ⟨hu, hc⟩
      refine ⟨ih hl hu, ?_⟩
      let c : ℝ := Rationals.q (certificate n).2.1
      let e : ℝ := ((2 : ℝ) ^ (certificate n).1)⁻¹
      change |c - (x : ℝ)| ≤ e
      change |c - (u : ℝ)| ≤ e at hc
      change |c - (l : ℝ)| ≤ e at hb
      exact abs_le.mpr ⟨(abs_le.mp hc).1.trans (sub_le_sub_left (show (x : ℝ) ≤ u from hxu) c),
        (sub_le_sub_left (show (l : ℝ) ≤ x from hlx) c).trans (abs_le.mp hb).2⟩
    · exact ih

/-- The intersection of all accepted closed approximation bands at a name. -/
@[no_expose] def nameInterval (d : ℕ) (p : Bits) : Set UnitInterval := ⋂ n, stage d p n

theorem nameInterval_nonempty (d : ℕ) (p : Bits) : (nameInterval d p).Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
    (stage_decreases d p) (stage_nonempty d p) (stage_closed d p 0).isCompact (stage_closed d p)

theorem nameInterval_graph_closed (d : ℕ) :
    IsClosed {z : Bits × UnitInterval | z.2 ∈ nameInterval d z.1} := by
  have he : {z : Bits × UnitInterval | z.2 ∈ nameInterval d z.1} =
      ⋂ n, {z : Bits × UnitInterval | z.2 ∈ stage d z.1 n} := by
    ext z
    simp [nameInterval]
  rw [he]
  exact isClosed_iInter (stage_graph_closed d)

theorem nameInterval_box (d : ℕ) (p : Bits) :
    ∃ l u : UnitInterval, l ≤ u ∧ nameInterval d p = Icc l u := by
  have hc : IsCompact (nameInterval d p) :=
    ((nameInterval_graph_closed d).preimage (continuous_const.prodMk continuous_id)).isCompact
  obtain ⟨l, hl⟩ := hc.exists_isLeast (nameInterval_nonempty d p)
  obtain ⟨u, hu⟩ := hc.exists_isGreatest (nameInterval_nonempty d p)
  refine ⟨l, u, hl.2 hu.1, Set.ext fun x => ⟨fun hx => ⟨hl.2 hx, hu.2 hx⟩, ?_⟩⟩
  rintro ⟨hlx, hxu⟩
  exact mem_iInter.mpr fun n =>
    stage_between d p hlx hxu n (mem_iInter.mp hl.1 n) (mem_iInter.mp hu.1 n)

private theorem mem_band_of_computes {d : ℕ} {p : Bits} {r : UnitInterval}
    (h : ComputesReal d p r) {t : Certificate} (ha : applies d t p) :
    r ∈ approximationBand t.1 t.2.1 := by
  obtain ⟨j, hj, hb⟩ := h t.1
  have hval := (numberedEval_graph d p t.1 t.2.1).2 ⟨t.2.2, ha⟩
  have he := Part.mem_unique hj hval
  exact he ▸ hb.le

private theorem mem_stage_of_computes {d : ℕ} {p : Bits} {r : UnitInterval}
    (h : ComputesReal d p r) (n : ℕ) : r ∈ stage d p n := by
  classical
  induction n with
  | zero => trivial
  | succ n ih =>
    simp only [stage, refineBand]
    split
    next ha => exact ⟨ih, mem_band_of_computes h ha.1⟩
    next => exact ih

/-- At a name computing a real, the accepted bands determine that real uniquely. -/
theorem nameInterval_singleton {d : ℕ} {p : Bits} {r : UnitInterval}
    (h : ComputesReal d p r) : nameInterval d p = {r} := by
  classical
  ext x
  constructor
  · intro hx
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    by_contra hne
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
      (show (0 : ℝ) < |(x : ℝ) - (r : ℝ)| / 2 from by
        have := abs_pos.mpr (sub_ne_zero.mpr hne)
        linarith)
      (show (2 : ℝ)⁻¹ < 1 by norm_num)
    rw [inv_pow] at hk
    obtain ⟨i, hi, hri⟩ := h k
    obtain ⟨w, hw⟩ := (numberedEval_graph d p k i).1 hi
    let n := Encodable.encode ((k, i, w) : Certificate)
    have he : certificate n = (k, i, w) := certificate_encode _
    have hap : applies d (k, i, w) p := hw
    have hr : r ∈ stage d p n ∩ approximationBand k i :=
      ⟨mem_stage_of_computes h n, hri.le⟩
    have hx' := (mem_iInter.mp hx) (n+1)
    change x ∈ refineBand d (certificate n) p (stage d p n) at hx'
    rw [he] at hx'
    have ha : applies d (k, i, w) p ∧ (stage d p n ∩ approximationBand k i).Nonempty :=
      ⟨hap, r, hr⟩
    rw [refineBand, ite_eq_left ha] at hx'
    have hxi : |(Rationals.q i : ℝ) - (x : ℝ)| ≤ ((2 : ℝ)^k)⁻¹ := hx'.2
    have htriangle := abs_sub_le (x : ℝ) (Rationals.q i : ℝ) (r : ℝ)
    rw [abs_sub_comm (x : ℝ) (Rationals.q i : ℝ)] at htriangle
    linarith
  · rintro rfl
    exact mem_iInter.mpr (mem_stage_of_computes h)

end CategoricalEssentialIncompleteness.V46.Miller
