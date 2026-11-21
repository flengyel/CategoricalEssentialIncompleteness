/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutDyadicBoxes
public import CategoricalEssentialIncompleteness.V46MillerCutSeries
public import Mathlib.Algebra.Order.Group.MinMax

/-! # Finite-box distances and their positive loci

The distance uses the weighted product formula. Each finite-box formula has a
constructed nearest point, rather than an assumed distance comparison. The empty union
has distance 1, as in the manuscript.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace CategoricalEssentialIncompleteness.V46.Miller.Cut.Distance

def intervalDistance (lo hi x : ℝ) : ℝ := max (max (lo-x) 0) (max (x-hi) 0)

theorem interval_nonneg (lo hi x : ℝ) : 0 ≤ intervalDistance lo hi x :=
  le_trans (le_max_right _ _) (le_max_left _ _)

theorem interval_zero_iff (lo hi x : ℝ) :
    intervalDistance lo hi x=0 ↔ lo≤x ∧ x≤hi := by
  constructor
  · intro h
    have hlo : lo-x≤0 := (le_max_left (lo-x) 0).trans
      ((le_max_left _ _).trans_eq h)
    have hhi : x-hi≤0 := (le_max_left (x-hi) 0).trans
      ((le_max_right _ _).trans_eq h)
    exact ⟨by linarith,by linarith⟩
  · rintro ⟨hl,hh⟩
    simp only [intervalDistance,max_eq_right (sub_nonpos.mpr hl),
      max_eq_right (sub_nonpos.mpr hh),max_self]

theorem interval_le_one (lo hi x : ℝ) (hl : lo≤1) (hh : 0≤hi)
    (hx : 0≤x ∧ x≤1) : intervalDistance lo hi x≤1 := by
  unfold intervalDistance
  exact max_le (max_le (by linarith) (by norm_num))
    (max_le (by linarith) (by norm_num))

theorem interval_le_abs (lo hi x y : ℝ) (hy : lo≤y ∧ y≤hi) :
    intervalDistance lo hi x≤|x-y| := by
  have ha : lo-x≤|x-y| := calc
    lo-x ≤ y-x := sub_le_sub_right hy.1 x
    _ ≤ |x-y| := by simpa only [abs_sub_comm] using le_abs_self (y-x)
  have hb : x-hi≤|x-y| := (sub_le_sub_left hy.2 x).trans (le_abs_self (x-y))
  exact max_le (max_le ha (abs_nonneg _)) (max_le hb (abs_nonneg _))

theorem interval_lipschitz (lo hi x y : ℝ) :
    |intervalDistance lo hi x-intervalDistance lo hi y|≤|x-y| := by
  have ha := abs_max_sub_max_le_abs (lo-x) (lo-y) 0
  have hb := abs_max_sub_max_le_abs (x-hi) (y-hi) 0
  have hea : (lo-x)-(lo-y)=y-x := by ring
  have heb : (x-hi)-(y-hi)=x-y := by ring
  rw [hea,abs_sub_comm y x] at ha
  rw [heb] at hb
  exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le ha hb)

def clamp (lo hi x : ℝ) : ℝ := max lo (min hi x)

theorem clamp_mem (lo hi x : ℝ) (h : lo≤hi) :
    lo≤clamp lo hi x ∧ clamp lo hi x≤hi :=
  ⟨le_max_left _ _,max_le h (min_le_left _ _)⟩

theorem interval_clamp (lo hi x : ℝ) (h : lo≤hi) :
    intervalDistance lo hi x=|x-clamp lo hi x| := by
  by_cases hxl : x≤lo
  · have hxh : x≤hi := hxl.trans h
    simp only [intervalDistance,clamp,min_eq_right hxh,max_eq_left hxl,
      max_eq_right (sub_nonpos.mpr hxh),
      max_eq_left (sub_nonneg.mpr hxl),abs_of_nonpos (sub_nonpos.mpr hxl)]
    ring
  · have hlx : lo≤x := le_of_not_ge hxl
    by_cases hhx : hi≤x
    · simp only [intervalDistance,clamp,min_eq_left hhx,max_eq_right h,
        max_eq_right (sub_nonpos.mpr hlx),max_eq_left (sub_nonneg.mpr hhx),
        max_eq_right (sub_nonneg.mpr hhx),abs_of_nonneg (sub_nonneg.mpr hhx)]
    · have hxh : x≤hi := le_of_not_ge hhx
      rw [(interval_zero_iff lo hi x).mpr ⟨hlx,hxh⟩]
      simp [clamp,min_eq_right hxh,max_eq_right hlx]

def boxDistance (c : Boxes.BoxCode) (z : Point) : ℝ :=
  ∑ n ∈ Finset.range c.1, Series.weight n * intervalDistance
    (Dyadic.value (Boxes.lowerCode c.1 c.2 n))
    (Dyadic.value (Boxes.upperCode c.1 c.2 n)) (z n)

theorem boxDistance_nonneg (c : Boxes.BoxCode) (z : Point) : 0≤boxDistance c z :=
  Finset.sum_nonneg (fun n _ => mul_nonneg (Series.weight_nonneg n) (interval_nonneg _ _ _))

theorem boxDistance_le_one (c : Boxes.BoxCode) (z : Point) : boxDistance c z≤1 := by
  calc
    boxDistance c z ≤ ∑ n ∈ Finset.range c.1, Series.weight n := by
      apply Finset.sum_le_sum
      intro n hn
      have he := Boxes.endpoint_bounds c.1 c.2 n
      exact mul_le_of_le_one_right (Series.weight_nonneg n)
        (interval_le_one _ _ _ (he.2.1.trans he.2.2) (he.1.trans he.2.1) (z n).property)
    _ ≤ ∑' n, Series.weight n := Summable.sum_le_tsum (Finset.range c.1)
      (fun n _ => Series.weight_nonneg n) Series.weight_summable
    _ = 1 := Series.weight_tsum

theorem boxDistance_zero_iff (c : Boxes.BoxCode) (z : Point) :
    boxDistance c z=0 ↔ z ∈ Boxes.box c.1 c.2 := by
  constructor
  · intro h n hn
    have hterm : Series.weight n * intervalDistance
        (Dyadic.value (Boxes.lowerCode c.1 c.2 n))
        (Dyadic.value (Boxes.upperCode c.1 c.2 n)) (z n) ≤ boxDistance c z := by
      unfold boxDistance
      exact Finset.single_le_sum (fun i _ => mul_nonneg (Series.weight_nonneg i)
        (interval_nonneg (Dyadic.value (Boxes.lowerCode c.1 c.2 i))
          (Dyadic.value (Boxes.upperCode c.1 c.2 i)) (z i))) (Finset.mem_range.mpr hn)
    have hz : intervalDistance (Dyadic.value (Boxes.lowerCode c.1 c.2 n))
        (Dyadic.value (Boxes.upperCode c.1 c.2 n)) (z n)=0 := by
      have hw := Series.weight_pos n
      have hd := interval_nonneg (Dyadic.value (Boxes.lowerCode c.1 c.2 n))
        (Dyadic.value (Boxes.upperCode c.1 c.2 n)) (z n)
      rw [h] at hterm
      nlinarith
    exact (interval_zero_iff _ _ _).mp hz
  · intro h
    apply Finset.sum_eq_zero
    intro n hn
    rw [(interval_zero_iff _ _ _).mpr (h n (Finset.mem_range.mp hn)),mul_zero]

theorem boxDistance_pos_iff (c : Boxes.BoxCode) (z : Point) :
    0<boxDistance c z ↔ z ∉ Boxes.box c.1 c.2 := by
  constructor
  · intro h hz
    have he := (boxDistance_zero_iff c z).mpr hz
    linarith
  · intro h
    exact lt_of_le_of_ne (boxDistance_nonneg c z)
      (fun he => h ((boxDistance_zero_iff c z).mp he.symm))

theorem continuous_boxDistance (c : Boxes.BoxCode) : Continuous (boxDistance c) := by
  unfold boxDistance intervalDistance
  fun_prop

/-- The exact metric formula for Q. -/
def productDistance (z w : Point) : ℝ := ∑' n,Series.weight n*|(z n:ℝ)-(w n:ℝ)|

private theorem productDistance_summable (z w : Point) :
    Summable (fun n => Series.weight n*|(z n:ℝ)-(w n:ℝ)|) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Series.weight_nonneg n) (abs_nonneg _)) _ Series.weight_summable
  intro n
  apply mul_le_of_le_one_right (Series.weight_nonneg n)
  have hz0 := (z n).property.1
  have hz1 := (z n).property.2
  have hw0 := (w n).property.1
  have hw1 := (w n).property.2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def nearest (c : Boxes.BoxCode) (z : Point) : Point := fun n =>
  if hn : n<c.1 then
    ⟨clamp (Dyadic.value (Boxes.lowerCode c.1 c.2 n))
      (Dyadic.value (Boxes.upperCode c.1 c.2 n)) (z n),
      by
        have hb := Boxes.endpoint_bounds c.1 c.2 n
        have hm := clamp_mem _ _ (z n) hb.2.1
        exact ⟨hb.1.trans hm.1,hm.2.trans hb.2.2⟩⟩
  else z n

theorem nearest_mem (c : Boxes.BoxCode) (z : Point) : nearest c z ∈ Boxes.box c.1 c.2 := by
  intro n hn
  simp only [nearest,dite_eq_left hn]
  exact clamp_mem _ _ (z n) (Boxes.endpoint_bounds c.1 c.2 n).2.1

theorem boxDistance_nearest (c : Boxes.BoxCode) (z : Point) :
    productDistance z (nearest c z)=boxDistance c z := by
  have hs : ∀ n ∉ Finset.range c.1,
      Series.weight n*|(z n:ℝ)-(nearest c z n:ℝ)|=0 := by
    intro n hn
    have hn' : ¬n<c.1 := by simpa only [Finset.mem_range] using hn
    simp [nearest,hn']
  rw [productDistance,tsum_eq_sum hs]
  apply Finset.sum_congr rfl
  intro n hn
  rw [nearest,dite_eq_left (Finset.mem_range.mp hn)]
  rw [← interval_clamp _ _ (z n) (Boxes.endpoint_bounds c.1 c.2 n).2.1]

theorem boxDistance_le_productDistance (c : Boxes.BoxCode) (z w : Point)
    (hw : w ∈ Boxes.box c.1 c.2) : boxDistance c z ≤ productDistance z w := by
  calc
    boxDistance c z ≤ ∑ n ∈ Finset.range c.1, Series.weight n*|(z n:ℝ)-(w n:ℝ)| :=
      Finset.sum_le_sum (fun n hn => mul_le_mul_of_nonneg_left
        (interval_le_abs _ _ _ _ (hw n (Finset.mem_range.mp hn))) (Series.weight_nonneg n))
    _ ≤ productDistance z w := Summable.sum_le_tsum (Finset.range c.1)
      (fun n _ => mul_nonneg (Series.weight_nonneg n) (abs_nonneg _))
      (productDistance_summable z w)

/-- Empty family convention is exactly 1. Nonempty families use their
finite minimum; all constituent distances are at most 1. -/
def familyDistance : List Boxes.BoxCode → Point → ℝ
  | [],_ => 1
  | c::L,z => min (boxDistance c z) (familyDistance L z)

theorem familyDistance_nonneg (L : List Boxes.BoxCode) (z : Point) : 0≤familyDistance L z := by
  induction L with
  | nil => norm_num [familyDistance]
  | cons c L ih => exact le_min (boxDistance_nonneg c z) ih

theorem familyDistance_le_one (L : List Boxes.BoxCode) (z : Point) : familyDistance L z≤1 := by
  cases L with
  | nil => exact le_rfl
  | cons c L => exact (min_le_left _ _).trans (boxDistance_le_one c z)

theorem familyDistance_pos_iff (L : List Boxes.BoxCode) (z : Point) :
    0<familyDistance L z ↔ z ∉ Boxes.union L := by
  induction L with
  | nil => simp [familyDistance,Boxes.union]
  | cons c L ih =>
    rw [familyDistance,lt_min_iff,boxDistance_pos_iff,ih]
    simp [Boxes.union,not_or]

theorem continuous_familyDistance (L : List Boxes.BoxCode) : Continuous (familyDistance L) := by
  induction L with
  | nil => exact continuous_const
  | cons c L ih => exact (continuous_boxDistance c).min ih

theorem familyDistance_le_box (L : List Boxes.BoxCode) (z : Point) (c : Boxes.BoxCode)
    (hc : c ∈ L) : familyDistance L z ≤ boxDistance c z := by
  induction L with
  | nil => cases hc
  | cons a L ih =>
    obtain rfl | hc := List.mem_cons.mp hc
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hc)

theorem familyDistance_attained (L : List Boxes.BoxCode) (hL : L≠[]) (z : Point) :
    ∃ c ∈ L, familyDistance L z=boxDistance c z := by
  induction L with
  | nil => exact (hL rfl).elim
  | cons c L ih =>
    by_cases he : L=[]
    · subst L
      exact ⟨c,by simp, min_eq_left (boxDistance_le_one c z)⟩
    · obtain ⟨b,hb,hv⟩ := ih he
      by_cases hcb : boxDistance c z ≤ familyDistance L z
      · exact ⟨c,by simp,min_eq_left hcb⟩
      · exact ⟨b,List.mem_cons_of_mem c hb,(min_eq_right (le_of_not_ge hcb)).trans hv⟩

/-- A nearest point witnesses the minimum distance to every nonempty finite union. No
minimum/distance property is a supplied premise. -/
theorem familyDistance_minimum (L : List Boxes.BoxCode) (hL : L≠[]) (z : Point) :
    (∃ w ∈ Boxes.union L, productDistance z w=familyDistance L z) ∧
      ∀ w ∈ Boxes.union L, familyDistance L z ≤ productDistance z w := by
  obtain ⟨c,hc,hmin⟩ := familyDistance_attained L hL z
  constructor
  · exact ⟨nearest c z,⟨c,hc,nearest_mem c z⟩,(boxDistance_nearest c z).trans hmin.symm⟩
  · rintro w ⟨b,hb,hw⟩
    exact (familyDistance_le_box L z b hb).trans (boxDistance_le_productDistance b z w hw)


theorem union_nonempty_iff (L : List Boxes.BoxCode) : (Boxes.union L).Nonempty ↔ L≠[] := by
  constructor
  · rintro ⟨z,hz⟩ hL
    simp [hL,Boxes.union] at hz
  · intro hL
    cases L with
    | nil => exact (hL rfl).elim
    | cons c L =>
      obtain ⟨z,hz⟩ := Boxes.box_nonempty c.1 c.2
      exact ⟨z,c,by simp,hz⟩

theorem weight_le_one (n : ℕ) : Series.weight n≤1 := by
  have h := Series.weight_summable.le_tsum n (fun m _ => Series.weight_nonneg m)
  simpa only [Series.weight_tsum] using h

/-- A concrete finite-coordinate error estimate. Its numerical sample is
constructed below; this is not a supplied real-computability field. -/
theorem boxDistance_error (c : Boxes.BoxCode) (z w : Point) (ε : ℝ) (hε : 0≤ε)
    (h : ∀ n<c.1, |(z n:ℝ)-(w n:ℝ)|≤ε) :
    |boxDistance c z-boxDistance c w|≤(c.1:ℝ)*ε := by
  rw [boxDistance,boxDistance,← Finset.sum_sub_distrib]
  calc
    |∑ n ∈ Finset.range c.1, (Series.weight n*intervalDistance
      (Dyadic.value (Boxes.lowerCode c.1 c.2 n)) (Dyadic.value (Boxes.upperCode c.1 c.2 n)) (z n)-
      Series.weight n*intervalDistance (Dyadic.value (Boxes.lowerCode c.1 c.2 n))
        (Dyadic.value (Boxes.upperCode c.1 c.2 n)) (w n))| ≤
        ∑ n ∈ Finset.range c.1, |Series.weight n*intervalDistance
          (Dyadic.value (Boxes.lowerCode c.1 c.2 n)) (Dyadic.value (Boxes.upperCode c.1 c.2 n)) (z n)-
          Series.weight n*intervalDistance (Dyadic.value (Boxes.lowerCode c.1 c.2 n))
            (Dyadic.value (Boxes.upperCode c.1 c.2 n)) (w n)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range c.1, ε := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← mul_sub,abs_mul,abs_of_nonneg (Series.weight_nonneg n)]
      calc
        _ ≤ Series.weight n*|(z n:ℝ)-(w n:ℝ)| :=
          mul_le_mul_of_nonneg_left (interval_lipschitz _ _ _ _) (Series.weight_nonneg n)
        _ ≤ Series.weight n*ε := mul_le_mul_of_nonneg_left
          (h n (Finset.mem_range.mp hn)) (Series.weight_nonneg n)
        _ ≤ ε := (mul_le_mul_of_nonneg_right (weight_le_one n) hε).trans_eq (one_mul ε)
    _ = (c.1:ℝ)*ε := by simp

theorem familyDistance_error (L : List Boxes.BoxCode) (D : ℕ) (z w : Point) (ε : ℝ)
    (hε : 0≤ε) (hD : ∀ c∈L,c.1≤D)
    (h : ∀ n<D, |(z n:ℝ)-(w n:ℝ)|≤ε) :
    |familyDistance L z-familyDistance L w|≤(D:ℝ)*ε := by
  induction L with
  | nil => simp only [familyDistance,sub_self,abs_zero]; positivity
  | cons c L ih =>
    have hc : |boxDistance c z-boxDistance c w|≤(D:ℝ)*ε :=
      (boxDistance_error c z w ε hε (fun n hn => h n (hn.trans_le (hD c (by simp))))).trans
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hD c (by simp)) hε)
    have ht := ih (fun b hb => hD b (List.mem_cons_of_mem c hb))
    exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le hc ht)

def delta (e m t : ℕ) (z : Point) : ℝ := familyDistance (Boxes.badBoxes e m t) z

theorem delta_bounds (e m t : ℕ) (z : Point) : 0≤delta e m t z ∧ delta e m t z≤1 :=
  ⟨familyDistance_nonneg _ z,familyDistance_le_one _ z⟩

theorem delta_pos_iff (e m t : ℕ) (z : Point) :
    0<delta e m t z ↔ z ∉ Cut.badImage e m t := by
  rw [delta,familyDistance_pos_iff,Boxes.badBoxes_spec]

theorem continuous_delta (e m t : ℕ) : Continuous (delta e m t) := continuous_familyDistance _


theorem delta_empty (e m t : ℕ) (h : Cut.badImage e m t=∅) : ∀ z,delta e m t z=1 := by
  have hL : Boxes.badBoxes e m t=[] := by
    by_contra hn
    obtain ⟨z,hz⟩ := (union_nonempty_iff _).mpr hn
    rw [Boxes.badBoxes_spec,h] at hz
    exact hz
  intro z
  simp only [delta,hL,familyDistance]

theorem delta_nonempty_minimum (e m t : ℕ) (h : (Cut.badImage e m t).Nonempty) (z : Point) :
    (∃ w∈Cut.badImage e m t, productDistance z w=delta e m t z) ∧
      ∀ w∈Cut.badImage e m t, delta e m t z≤productDistance z w := by
  have hL : Boxes.badBoxes e m t≠[] := (union_nonempty_iff _).mp (by
    rwa [Boxes.badBoxes_spec])
  simpa only [delta,Boxes.badBoxes_spec] using familyDistance_minimum _ hL z

end CategoricalEssentialIncompleteness.V46.Miller.Cut.Distance
