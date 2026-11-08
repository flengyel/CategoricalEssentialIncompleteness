/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerCutBoxDistance
import CategoricalEssentialIncompleteness.V46MillerFiniteUse

/-! # Effective finite rational approximation of the actual bad-set distance

Only finite binary words and natural-number dyadic codes are computed.
The infinite point and its real coordinates occur in the correctness proof.
The use bound contains every queried bit, for every binary oracle.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open Encodable Denumerable
namespace CategoricalEssentialIncompleteness.V46.Miller.Cut.Distance

def sampleCode (u : Word) (n r : ℕ) : Dyadic.Code := (wordNumeral u n r,r)

def samplePoint (u : Word) (r : ℕ) : Point := fun n =>
  ⟨Dyadic.value (sampleCode u n r),Dyadic.value_nonneg _,by
    apply (div_le_one (by positivity : (0:ℝ)<2^r)).mpr
    exact_mod_cast (Boxes.numeral_lt_pow (wordDigits u n) r).le⟩

theorem samplePoint_error (p : Bits) (N n r : ℕ) (hN : queryBound n r≤N) :
    |(samplePoint (bitPrefix p N) r n:ℝ)-(rho p n:ℝ)|≤((2:ℝ)^r)⁻¹ := by
  have hl : ∀ j<r,Nat.pair n j<N := fun j hj =>
    (query_lt_bound n r j hj).trans_le hN
  have hw := wordNumeral_prefix p N n r hl
  have hb := numeral_bounds (fun j => p (Nat.pair n j)) r
  change |(wordNumeral (bitPrefix p N) n r:ℝ)/(2:ℝ)^r-
    Real.ofDigits (fun j => p (Nat.pair n j))|≤_
  rw [hw,abs_of_nonpos (sub_nonpos.mpr hb.1)]
  rw [add_div,one_div] at hb
  linarith

def termCode (u : Word) (c : Boxes.BoxCode) (r n : ℕ) : Dyadic.Code :=
  Dyadic.shift (Dyadic.interval (Boxes.lowerCode c.1 c.2 n) (Boxes.upperCode c.1 c.2 n)
    (sampleCode u n r)) (n+1)

def boxLoop (u : Word) (c : Boxes.BoxCode) (r : ℕ) : ℕ → Dyadic.Code
  | 0 => Dyadic.zero
  | n+1 => Dyadic.add (boxLoop u c r n) (termCode u c r n)

def boxApprox (u : Word) (c : Boxes.BoxCode) (r : ℕ) : Dyadic.Code := boxLoop u c r c.1

private theorem termCode_value (u : Word) (c : Boxes.BoxCode) (r n : ℕ) :
    Dyadic.value (termCode u c r n) = Series.weight n * intervalDistance
      (Dyadic.value (Boxes.lowerCode c.1 c.2 n)) (Dyadic.value (Boxes.upperCode c.1 c.2 n))
      (samplePoint u r n) := by
  rw [termCode,Dyadic.value_shift,Dyadic.value_interval,Series.weight_eq]
  simp only [intervalDistance,samplePoint,div_eq_mul_inv,mul_comm]

theorem boxApprox_value (u : Word) (c : Boxes.BoxCode) (r : ℕ) :
    Dyadic.value (boxApprox u c r)=boxDistance c (samplePoint u r) := by
  have h : ∀ k,Dyadic.value (boxLoop u c r k)=∑ n∈Finset.range k,
      Series.weight n*intervalDistance (Dyadic.value (Boxes.lowerCode c.1 c.2 n))
        (Dyadic.value (Boxes.upperCode c.1 c.2 n)) (samplePoint u r n) := by
    intro k
    induction k with
    | zero => simp [boxLoop]
    | succ k ih => rw [boxLoop,Dyadic.value_add,ih,termCode_value,Finset.sum_range_succ]
  exact h c.1

def familyApprox (u : Word) (r : ℕ) (L : List Boxes.BoxCode) : Dyadic.Code :=
  L.foldr (fun c a => Dyadic.minCode (boxApprox u c r) a) Dyadic.one

theorem familyApprox_value (u : Word) (r : ℕ) (L : List Boxes.BoxCode) :
    Dyadic.value (familyApprox u r L)=familyDistance L (samplePoint u r) := by
  induction L with
  | nil => exact Dyadic.value_one
  | cons c L ih =>
    simp only [familyApprox,List.foldr_cons,Dyadic.value_minCode,boxApprox_value,familyDistance]
    exact congrArg (min (boxDistance c (samplePoint u r))) ih

def approxCode (u : Word) (e m t r : ℕ) : Dyadic.Code :=
  familyApprox u r (Boxes.badBoxes e m t)

theorem approxCode_value (u : Word) (e m t r : ℕ) :
    Dyadic.value (approxCode u e m t r)=delta e m t (samplePoint u r) :=
  familyApprox_value _ _ _

def dimension (L : List Boxes.BoxCode) : ℕ := L.foldr (fun c D => max c.1 D) 0

theorem dimension_bound (L : List Boxes.BoxCode) (c : Boxes.BoxCode) (hc : c∈L) : c.1≤dimension L := by
  induction L with
  | nil => cases hc
  | cons b L ih =>
    obtain rfl | hc := List.mem_cons.mp hc
    · exact le_max_left _ _
    · exact (ih hc).trans (le_max_right _ _)

def queryUse (D r : ℕ) : ℕ :=
  (List.range D).foldr (fun n N => max (queryBound n r) N) 0

private theorem member_le_foldMax (L : List ℕ) (f : ℕ → ℕ) (n : ℕ) (hn : n∈L) :
    f n≤L.foldr (fun k N => max (f k) N) 0 := by
  induction L with
  | nil => cases hn
  | cons k L ih =>
    obtain rfl | hn := List.mem_cons.mp hn
    · exact le_max_left _ _
    · exact (ih hn).trans (le_max_right _ _)

theorem queryBound_le_use (D r n : ℕ) (hn : n<D) : queryBound n r≤queryUse D r :=
  member_le_foldMax (List.range D) (fun k => queryBound k r) n (List.mem_range.mpr hn)

theorem approxCode_error (p : Bits) (N e m t r : ℕ)
    (hN : queryUse (dimension (Boxes.badBoxes e m t)) r≤N) :
    |Dyadic.value (approxCode (bitPrefix p N) e m t r)-delta e m t (rho p)|≤
      (dimension (Boxes.badBoxes e m t):ℝ)*((2:ℝ)^r)⁻¹ := by
  rw [approxCode_value]
  apply familyDistance_error _ _ _ _ _ (by positivity)
    (fun c hc => dimension_bound _ c hc)
  intro n hn
  exact samplePoint_error p N n r ((queryBound_le_use _ r n hn).trans hN)

private theorem nat_le_pow_two (n : ℕ) : n≤2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hp : 0<2^n := by positivity
    omega

def precision (e m t k : ℕ) : ℕ := k+dimension (Boxes.badBoxes e m t)+2

def use (e m t k : ℕ) : ℕ := queryUse (dimension (Boxes.badBoxes e m t)) (precision e m t k)

theorem approxCode_precision_error (p : Bits) (N e m t k : ℕ) (hN : use e m t k≤N) :
    |Dyadic.value (approxCode (bitPrefix p N) e m t (precision e m t k))-
      delta e m t (rho p)|≤((2:ℝ)^(k+2))⁻¹ := by
  apply (approxCode_error p N e m t (precision e m t k) hN).trans
  let D := dimension (Boxes.badBoxes e m t)
  have hD : (D:ℝ)≤(2:ℝ)^D := by exact_mod_cast nat_le_pow_two D
  have hr : (D:ℝ)/(2:ℝ)^D≤1 := (div_le_one (by positivity)).mpr hD
  calc
    (D:ℝ)*((2:ℝ)^(k+D+2))⁻¹ = ((D:ℝ)/(2:ℝ)^D)*((2:ℝ)^(k+2))⁻¹ := by
      rw [show k+D+2=D+(k+2) by omega,pow_add,mul_inv]
      ring
    _ ≤ 1*((2:ℝ)^(k+2))⁻¹ := mul_le_mul_of_nonneg_right hr (by positivity)
    _ = _ := one_mul _

/- Ordinary numerical algorithms. These proofs expose the finite operations
rather than assuming a real-computability or oracle-realizability field. -/
private theorem lowerCode_primrec : Primrec (fun a : Boxes.BoxCode × ℕ => Boxes.lowerCode a.1.1 a.1.2 a.2) := by
  have hp : Primrec (fun a : Boxes.BoxCode × ℕ => (((a.1.2,a.1.1),a.2),a.1.1)) :=
    Primrec.pair (Primrec.pair
      (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst)) Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
  exact Primrec.pair (Boxes.rowNumeral_primrec.comp hp) (Primrec.fst.comp Primrec.fst)

private theorem upperCode_primrec : Primrec (fun a : Boxes.BoxCode × ℕ => Boxes.upperCode a.1.1 a.1.2 a.2) := by
  have hp : Primrec (fun a : Boxes.BoxCode × ℕ => (((a.1.2,a.1.1),a.2),a.1.1)) :=
    Primrec.pair (Primrec.pair
      (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst)) Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
  exact Primrec.pair (Primrec.succ.comp (Boxes.rowNumeral_primrec.comp hp))
    (Primrec.fst.comp Primrec.fst)

private theorem sampleCode_primrec : Primrec (fun a : (Word × ℕ) × ℕ => sampleCode a.1.1 a.1.2 a.2) :=
  Primrec.pair wordNumeral_primrec Primrec.snd

private theorem termCode_primrec :
    Primrec (fun a : ((Word × Boxes.BoxCode) × ℕ) × ℕ => termCode a.1.1.1 a.1.1.2 a.1.2 a.2) := by
  let A := ((Word × Boxes.BoxCode) × ℕ) × ℕ
  have hu : Primrec (fun a : A => a.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hc : Primrec (fun a : A => a.1.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hr : Primrec (fun a : A => a.1.2) := Primrec.snd.comp Primrec.fst
  have hlo := lowerCode_primrec.comp (Primrec.pair hc Primrec.snd)
  have hhi := upperCode_primrec.comp (Primrec.pair hc Primrec.snd)
  have hx := sampleCode_primrec.comp (Primrec.pair (Primrec.pair hu Primrec.snd) hr)
  exact Dyadic.shift_primrec.comp
    (Dyadic.interval_primrec.comp (Primrec.pair (Primrec.pair hlo hhi) hx))
    (Primrec.succ.comp Primrec.snd)

private theorem boxLoop_primrec :
    Primrec (fun a : ((Word × Boxes.BoxCode) × ℕ) × ℕ => boxLoop a.1.1.1 a.1.1.2 a.1.2 a.2) := by
  let P := (Word × Boxes.BoxCode) × ℕ
  have ht : Primrec (fun a : P × (ℕ × Dyadic.Code) => termCode a.1.1.1 a.1.1.2 a.1.2 a.2.1) :=
    (termCode_primrec.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))).of_eq
      (fun _ => rfl)
  have hs := Dyadic.add_primrec.comp (Primrec.snd.comp Primrec.snd) ht
  refine Primrec.of_eq (Primrec.nat_rec (Primrec.const Dyadic.zero) hs.to₂) ?_
  intro a
  induction a.2 with
  | zero => rfl
  | succ n ih => exact congrArg (fun v => Dyadic.add v (termCode a.1.1.1 a.1.1.2 a.1.2 n)) ih

private theorem boxApprox_primrec :
    Primrec (fun a : (Word × Boxes.BoxCode) × ℕ => boxApprox a.1.1 a.1.2 a.2) :=
  (boxLoop_primrec.comp (Primrec.pair Primrec.id
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))).of_eq (fun _ => rfl)

private theorem familyApprox_primrec :
    Primrec (fun a : (Word × ℕ) × List Boxes.BoxCode => familyApprox a.1.1 a.1.2 a.2) := by
  let A := (Word × ℕ) × List Boxes.BoxCode
  have hp : Primrec (fun a : A × (Boxes.BoxCode × Dyadic.Code) =>
      ((a.1.1.1,a.2.1),a.1.1.2)) :=
    Primrec.pair (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  exact (Primrec.list_foldr Primrec.snd (Primrec.const Dyadic.one)
    (Dyadic.minCode_primrec.comp (boxApprox_primrec.comp hp) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      (fun _ => rfl)

abbrev Params := (ℕ × ℕ) × (ℕ × ℕ)

private theorem badBoxes_params_primrec :
    Primrec (fun a : Params => Boxes.badBoxes a.1.1 a.1.2 a.2.1) :=
  Boxes.badBoxes_primrec.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))

theorem approxCode_primrec : Primrec (fun a : Word × Params =>
    approxCode a.1 a.2.1.1 a.2.1.2 a.2.2.1 a.2.2.2) := by
  have hp : Primrec (fun a : Word × Params =>
      ((a.1,a.2.2.2),Boxes.badBoxes a.2.1.1 a.2.1.2 a.2.2.1)) :=
    Primrec.pair (Primrec.pair Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (badBoxes_params_primrec.comp Primrec.snd)
  exact (familyApprox_primrec.comp hp).of_eq (fun _ => rfl)

theorem dimension_primrec : Primrec dimension :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

private theorem queryBound_primrec : Primrec₂ queryBound := by
  have hs : Primrec (fun a : ℕ × (ℕ × ℕ) => max a.2.2 (Nat.pair a.1 a.2.1+1)) :=
    Primrec.nat_max.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.succ.comp (Primrec₂.natPair.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))
  refine Primrec.of_eq (Primrec.nat_rec (Primrec.const 0) hs.to₂) ?_
  intro a
  induction a.2 with
  | zero => rfl
  | succ n ih => exact congrArg (fun N => max N (Nat.pair a.1 n+1)) ih

theorem queryUse_primrec : Primrec₂ queryUse :=
  (Primrec.list_foldr (Primrec.list_range.comp Primrec.fst) (Primrec.const 0)
    (Primrec.nat_max.comp
      (queryBound_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq (fun _ => rfl)

private theorem dimension_params_primrec :
    Primrec (fun a : Params => dimension (Boxes.badBoxes a.1.1 a.1.2 a.2.1)) :=
  dimension_primrec.comp badBoxes_params_primrec

theorem precision_primrec : Primrec (fun a : Params => precision a.1.1 a.1.2 a.2.1 a.2.2) :=
  Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd) dimension_params_primrec) (Primrec.const 2)

theorem use_primrec : Primrec (fun a : Params => use a.1.1 a.1.2 a.2.1 a.2.2) :=
  queryUse_primrec.comp dimension_params_primrec precision_primrec

/-- A finite rational output index, using Root's concrete fixed q. -/
def finiteIndex (u : Word) (a : Params) : ℕ :=
  Dyadic.outputIndex (approxCode u a.1.1 a.1.2 a.2.1 (precision a.1.1 a.1.2 a.2.1 a.2.2))

theorem finiteIndex_primrec : Primrec₂ finiteIndex := by
  have hp : Primrec (fun a : Word × Params =>
      (a.1,(a.2.1,(a.2.2.1,precision a.2.1.1 a.2.1.2 a.2.2.1 a.2.2.2)))) :=
    Primrec.pair Primrec.fst (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (precision_primrec.comp Primrec.snd)))
  exact (Dyadic.outputIndex_primrec.comp (approxCode_primrec.comp hp)).of_eq (fun _ => rfl)

end CategoricalEssentialIncompleteness.V46.Miller.Cut.Distance
