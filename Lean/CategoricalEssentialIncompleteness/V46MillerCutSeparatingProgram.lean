/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutDistanceApproximation
public import CategoricalEssentialIncompleteness.V46MillerCutSeparatingReal

/-! # One ordinary index computing the actual separating real on every oracle

The numerical algorithm sums the first k+6 dyadic distance approximations
in each parity. It reads one finite prefix long enough for every term's
constructed use bound. Both that bound and the rational-index algorithm
are ordinary primitive-recursive functions. Rational indices need not be
constant on a representation fiber; the error is relative to one real.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
namespace CategoricalEssentialIncompleteness.V46.Miller.Cut

namespace SeparatingProgram

def count (k : ℕ) : ℕ := k+6

def termApprox (u : Word) (e i k j : ℕ) : Dyadic.Code :=
  Distance.approxCode u e (termOutput i j) (termStage j)
    (Distance.precision e (termOutput i j) (termStage j) (count k))

def termUse (e i k j : ℕ) : ℕ :=
  Distance.use e (termOutput i j) (termStage j) (count k)

def weightedTerm (u : Word) (e i k j : ℕ) : Dyadic.Code :=
  Dyadic.shift (termApprox u e i k j) (j+1)

def sumLoop (u : Word) (e i k : ℕ) : ℕ → Dyadic.Code
  | 0 => Dyadic.zero
  | j+1 => Dyadic.add (sumLoop u e i k j) (weightedTerm u e i k j)

def sumCode (u : Word) (e i k : ℕ) : Dyadic.Code := sumLoop u e i k (count k)

def seriesUse (e i k : ℕ) : ℕ :=
  (List.range (count k)).foldr (fun j N => max (termUse e i k j) N) 0

def use (e k : ℕ) : ℕ := max (seriesUse e 0 k) (seriesUse e 1 k)

def index (u : Word) (e k : ℕ) : ℕ :=
  Dyadic.outputIndex (Dyadic.separator (sumCode u e 0 k) (sumCode u e 1 k))

theorem termApprox_bounds (u : Word) (e i k j : ℕ) :
    0≤Dyadic.value (termApprox u e i k j) ∧ Dyadic.value (termApprox u e i k j)≤1 := by
  rw [termApprox,Distance.approxCode_value]
  exact Distance.delta_bounds _ _ _ _

theorem weightedTerm_value (u : Word) (e i k j : ℕ) :
    Dyadic.value (weightedTerm u e i k j)=Series.weight j*Dyadic.value (termApprox u e i k j) := by
  rw [weightedTerm,Dyadic.value_shift,Series.weight_eq]
  exact (div_eq_mul_inv _ _).trans (mul_comm _ _)

theorem sumLoop_value (u : Word) (e i k J : ℕ) :
    Dyadic.value (sumLoop u e i k J)=
      ∑ j∈Finset.range J,Series.weight j*Dyadic.value (termApprox u e i k j) := by
  induction J with
  | zero => simp only [sumLoop,Dyadic.value_zero,Finset.range_zero,Finset.sum_empty]
  | succ J ih =>
    rw [sumLoop,Dyadic.value_add,ih,weightedTerm_value,Finset.sum_range_succ]

theorem sumCode_value (u : Word) (e i k : ℕ) :
    Dyadic.value (sumCode u e i k)=
      ∑ j∈Finset.range (count k),Series.weight j*Dyadic.value (termApprox u e i k j) :=
  sumLoop_value u e i k (count k)

theorem sumCode_le_one (u : Word) (e i k : ℕ) : Dyadic.value (sumCode u e i k)≤1 := by
  rw [sumCode_value]
  apply le_trans _ (Series.weight_partial_le_one (count k))
  exact Finset.sum_le_sum (fun j _ =>
    mul_le_of_le_one_right (Series.weight_nonneg j) (termApprox_bounds u e i k j).2)

private theorem foldMax_bound (L : List ℕ) (f : ℕ → ℕ) (j : ℕ) (hj : j∈L) :
    f j≤L.foldr (fun n N => max (f n) N) 0 := by
  induction L with
  | nil => cases hj
  | cons n L ih =>
    obtain rfl | hj := List.mem_cons.mp hj
    · exact le_max_left _ _
    · exact (ih hj).trans (le_max_right _ _)

theorem termUse_le (e i k j : ℕ) (hj : j<count k) : termUse e i k j≤seriesUse e i k :=
  foldMax_bound _ _ j (List.mem_range.mpr hj)

theorem termApprox_error (p : Bits) (N e k : ℕ) (i : Fin 2) (j : ℕ)
    (hN : termUse e i.val k j≤N) :
    |deltaTerm e i j (rho p)-Dyadic.value (termApprox (bitPrefix p N) e i.val k j)|≤
      ((2:ℝ)^(k+8))⁻¹ := by
  have h := Distance.approxCode_precision_error p N e (termOutput i.val j)
    (termStage j) (count k) hN
  simpa only [termApprox,deltaTerm,count,Nat.add_assoc,abs_sub_comm] using h

theorem sumCode_error (p : Bits) (N e k : ℕ) (i : Fin 2)
    (hN : seriesUse e i.val k≤N) :
    |Dyadic.value (sumCode (bitPrefix p N) e i.val k)-Series.value (deltaTerm e i) (rho p)|≤
      ((2:ℝ)^(k+6))⁻¹+((2:ℝ)^(k+8))⁻¹ := by
  rw [sumCode_value,abs_sub_comm]
  exact Series.full_approximation_error (deltaTerm e i) (deltaTerm_bounds e i)
    (count k) (rho p)
    (fun j => Dyadic.value (termApprox (bitPrefix p N) e i.val k j))
    (((2:ℝ)^(k+8))⁻¹) (by positivity)
    (fun j hj => termApprox_error p N e k i j ((termUse_le _ _ _ _ hj).trans hN))

private theorem separator_error (s0 s1 g0 g1 : ℝ) :
    |(1/2+(s1-s0)/4)-(1/2+(g1-g0)/4)|≤(|s1-g1|+|s0-g0|)/4 := by
  have he : (1/2+(s1-s0)/4)-(1/2+(g1-g0)/4)=((s1-g1)-(s0-g0))/4 := by ring
  rw [he,abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)]
  exact div_le_div_of_nonneg_right (abs_sub _ _) (by norm_num)

private theorem error_strict (k : ℕ) :
    ((((2:ℝ)^(k+6))⁻¹+((2:ℝ)^(k+8))⁻¹)+
      (((2:ℝ)^(k+6))⁻¹+((2:ℝ)^(k+8))⁻¹))/4 < ((2:ℝ)^k)⁻¹ := by
  have hp : (0:ℝ)<2^k := by positivity
  have h6 : ((2:ℝ)^(k+6))⁻¹=((2:ℝ)^k)⁻¹/64 := by
    rw [pow_add]
    norm_num
    field_simp
  have h8 : ((2:ℝ)^(k+8))⁻¹=((2:ℝ)^k)⁻¹/256 := by
    rw [pow_add]
    norm_num
    field_simp
  rw [h6,h8]
  have hi := inv_pos.mpr hp
  nlinarith

/-- The finite ordinary algorithm is correct for every binary oracle.
Only its represented real, not the particular rational index, is fixed. -/
theorem index_error (p : Bits) (N e k : ℕ) (hN : use e k≤N) :
    |(Rationals.q (index (bitPrefix p N) e k):ℝ)-separatingReal e (rho p)|<((2:ℝ)^k)⁻¹ := by
  have h0 := sumCode_error p N e k 0 ((le_max_left _ _).trans hN)
  have h1 := sumCode_error p N e k 1 ((le_max_right _ _).trans hN)
  rw [index,Dyadic.outputIndex_value,Dyadic.value_separator _ _
    (sumCode_le_one _ _ _ _)]
  change |(1/2+(_-_)/4)-(1/2+(_-_)/4)|<_
  exact (separator_error _ _ _ _).trans_lt
    ((div_le_div_of_nonneg_right (add_le_add h1 h0) (by norm_num)).trans_lt (error_strict k))

/-! Ordinary numerical realizability of the finite algorithm. -/

abbrev Parameters := (ℕ × ℕ) × ℕ
abbrev TermParameters := (ℕ × ℕ) × (ℕ × ℕ)

theorem count_primrec : Primrec count := Primrec.nat_add.comp Primrec.id (Primrec.const 6)

theorem termApprox_primrec : Primrec (fun a : Word × TermParameters =>
    termApprox a.1 a.2.1.1 a.2.1.2 a.2.2.1 a.2.2.2) := by
  let A := Word × TermParameters
  have hu : Primrec (fun a : A => a.1) := Primrec.fst
  have he : Primrec (fun a : A => a.2.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hi : Primrec (fun a : A => a.2.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hk : Primrec (fun a : A => a.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hj : Primrec (fun a : A => a.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hm := termOutput_primrec.comp hi hj
  have ht := termStage_primrec.comp hj
  have hp := Primrec.pair (Primrec.pair he hm) (Primrec.pair ht (count_primrec.comp hk))
  have hr := Distance.precision_primrec.comp hp
  exact (Distance.approxCode_primrec.comp
    (Primrec.pair hu (Primrec.pair (Primrec.pair he hm) (Primrec.pair ht hr)))).of_eq (fun _ => rfl)

theorem termUse_primrec : Primrec (fun a : TermParameters => termUse a.1.1 a.1.2 a.2.1 a.2.2) := by
  have he : Primrec (fun a : TermParameters => a.1.1) := Primrec.fst.comp Primrec.fst
  have hi : Primrec (fun a : TermParameters => a.1.2) := Primrec.snd.comp Primrec.fst
  have hk : Primrec (fun a : TermParameters => a.2.1) := Primrec.fst.comp Primrec.snd
  have hj : Primrec (fun a : TermParameters => a.2.2) := Primrec.snd.comp Primrec.snd
  exact (Distance.use_primrec.comp (Primrec.pair
    (Primrec.pair he (termOutput_primrec.comp hi hj))
    (Primrec.pair (termStage_primrec.comp hj) (count_primrec.comp hk)))).of_eq (fun _ => rfl)

private theorem weightedTerm_primrec : Primrec (fun a : Word × TermParameters =>
    weightedTerm a.1 a.2.1.1 a.2.1.2 a.2.2.1 a.2.2.2) :=
  Dyadic.shift_primrec.comp termApprox_primrec
    (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

private theorem sumLoop_primrec : Primrec (fun a : (Word × Parameters) × ℕ =>
    sumLoop a.1.1 a.1.2.1.1 a.1.2.1.2 a.1.2.2 a.2) := by
  let A := Word × Parameters
  have hp : Primrec (fun a : A × (ℕ × Dyadic.Code) =>
      (a.1.1,(a.1.2.1,(a.1.2.2,a.2.1)))) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)))
  have hs := Dyadic.add_primrec.comp (Primrec.snd.comp Primrec.snd)
    (weightedTerm_primrec.comp hp)
  refine Primrec.of_eq (Primrec.nat_rec (Primrec.const Dyadic.zero) hs.to₂) ?_
  intro a
  induction a.2 with
  | zero => rfl
  | succ j ih => exact congrArg (fun v =>
      Dyadic.add v (weightedTerm a.1.1 a.1.2.1.1 a.1.2.1.2 a.1.2.2 j)) ih

theorem sumCode_primrec : Primrec (fun a : Word × Parameters =>
    sumCode a.1 a.2.1.1 a.2.1.2 a.2.2) :=
  (sumLoop_primrec.comp (Primrec.pair Primrec.id
    (count_primrec.comp (Primrec.snd.comp Primrec.snd)))).of_eq (fun _ => rfl)

theorem seriesUse_primrec : Primrec (fun a : Parameters => seriesUse a.1.1 a.1.2 a.2) := by
  have hp : Primrec (fun a : Parameters × (ℕ × ℕ) => (a.1.1,(a.1.2,a.2.1))) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
  exact (Primrec.list_foldr (Primrec.list_range.comp (count_primrec.comp Primrec.snd))
    (Primrec.const 0) (Primrec.nat_max.comp
      (termUse_primrec.comp hp) (Primrec.snd.comp Primrec.snd)).to₂).of_eq (fun _ => rfl)

theorem use_primrec : Primrec₂ use := by
  have h0 : Primrec (fun a:ℕ×ℕ => ((a.1,0),a.2)) :=
    Primrec.pair (Primrec.pair Primrec.fst (Primrec.const 0)) Primrec.snd
  have h1 : Primrec (fun a:ℕ×ℕ => ((a.1,1),a.2)) :=
    Primrec.pair (Primrec.pair Primrec.fst (Primrec.const 1)) Primrec.snd
  exact Primrec.of_eq (Primrec.nat_max.comp
    (seriesUse_primrec.comp h0) (seriesUse_primrec.comp h1)) (fun _ => rfl)

theorem index_primrec : Primrec (fun a : Word × (ℕ × ℕ) => index a.1 a.2.1 a.2.2) := by
  have h0 : Primrec (fun a : Word × (ℕ × ℕ) => (a.1,((a.2.1,0),a.2.2))) :=
    Primrec.pair Primrec.fst (Primrec.pair
      (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.const 0)) (Primrec.snd.comp Primrec.snd))
  have h1 : Primrec (fun a : Word × (ℕ × ℕ) => (a.1,((a.2.1,1),a.2.2))) :=
    Primrec.pair Primrec.fst (Primrec.pair
      (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.const 1)) (Primrec.snd.comp Primrec.snd))
  exact (Dyadic.outputIndex_primrec.comp (Dyadic.separator_primrec.comp
    (sumCode_primrec.comp h0) (sumCode_primrec.comp h1))).of_eq (fun _ => rfl)

def encodedUse (n : ℕ) : ℕ := use (Nat.unpair n).1 (Nat.unpair n).2

def encodedAlgorithm (a : List ℕ × ℕ) : ℕ :=
  index (normalizeWord a.1) (Nat.unpair a.2).1 (Nat.unpair a.2).2

theorem encodedUse_computable : Computable encodedUse :=
  (use_primrec.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)).to_comp

theorem encodedAlgorithm_computable : Computable encodedAlgorithm :=
  (index_primrec.comp (Primrec.pair (normalizeWord_primrec.comp Primrec.fst)
    (Primrec.unpair.comp Primrec.snd))).to_comp

end SeparatingProgram

/-- A single actual program is selected before every representation and
both numerical parameters. The theorem compares rational VALUES with the
same separating real; it does not equate outputs across representations. -/
theorem separatingReal_program :
    ∃ d : ℕ,∀ p : Bits,∀ e k : ℕ,∃ i : ℕ,
      i∈OracleProgram.numberedEval d p (Nat.pair e k) ∧
      |(Rationals.q i:ℝ)-separatingReal e (rho p)|<((2:ℝ)^k)⁻¹ := by
  obtain ⟨d,hd⟩ := FiniteUse.exists_program SeparatingProgram.encodedUse
    SeparatingProgram.encodedAlgorithm SeparatingProgram.encodedUse_computable
    SeparatingProgram.encodedAlgorithm_computable
  refine ⟨d,?_⟩
  intro p e k
  let N := SeparatingProgram.use e k
  let i := SeparatingProgram.index (bitPrefix p N) e k
  have hv : OracleProgram.numberedEval d p (Nat.pair e k)=Part.some i := by
    simpa only [SeparatingProgram.encodedUse,SeparatingProgram.encodedAlgorithm,
      Nat.unpair_pair,OracleProgram.numericalPrefix,normalizeWord_numericalPrefix] using hd p (Nat.pair e k)
  refine ⟨i,?_,SeparatingProgram.index_error p N e k (le_refl N)⟩
  rw [hv]
  exact Part.mem_some _

end CategoricalEssentialIncompleteness.V46.Miller.Cut
