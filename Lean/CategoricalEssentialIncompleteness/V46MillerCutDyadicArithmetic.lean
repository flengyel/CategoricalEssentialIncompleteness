/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRationalCodes
public import Mathlib.Algebra.Order.Group.MinMax

/-! # Ordinary numerical arithmetic on nonnegative dyadic fractions

A pair (a,k) denotes a/2^k. No computability instance for Rat or Real is
assumed. All operations below are actual primitive-recursive functions on
pairs of natural numbers; their rational-output semantics uses the fixed
ordinary enumeration from Miller.Rationals.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CategoricalEssentialIncompleteness.V46.Miller.Cut.Dyadic

abbrev Code := ℕ × ℕ

def value (a : Code) : ℝ := (a.1 : ℝ)/(2 : ℝ)^a.2

def zero : Code := (0,0)
def one : Code := (1,0)
def two : Code := (2,0)

def add (a b : Code) : Code := (a.1*2^b.2+b.1*2^a.2,a.2+b.2)
def positiveSub (a b : Code) : Code := (a.1*2^b.2-b.1*2^a.2,a.2+b.2)
def smaller (a b : Code) : Prop := a.1*2^b.2 ≤ b.1*2^a.2
instance smaller_decidable : DecidableRel smaller := fun a b =>
  inferInstanceAs (Decidable (a.1*2^b.2 ≤ b.1*2^a.2))

def minCode (a b : Code) : Code := if smaller a b then a else b
def maxCode (a b : Code) : Code := if smaller a b then b else a

def shift (a : Code) (k : ℕ) : Code := (a.1,a.2+k)

def interval (lo hi x : Code) : Code := maxCode (positiveSub lo x) (positiveSub x hi)

def separator (g0 g1 : Code) : Code := shift (positiveSub (add two g1) g0) 2

def outputIndex (a : Code) : ℕ := Rationals.dyadicIndex a.1 a.2

@[simp] theorem value_zero : value zero = 0 := by simp [value,zero]
@[simp] theorem value_one : value one = 1 := by simp [value,one]
@[simp] theorem value_two : value two = 2 := by simp [value,two]

theorem value_nonneg (a : Code) : 0 ≤ value a := by unfold value; positivity

theorem value_add (a b : Code) : value (add a b) = value a+value b := by
  simp only [value,add,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_add]
  field_simp

theorem value_le_iff (a b : Code) : value a ≤ value b ↔ smaller a b := by
  unfold value smaller
  rw [div_le_div_iff₀ (by positivity : (0:ℝ)<2^a.2) (by positivity : (0:ℝ)<2^b.2)]
  constructor <;> intro h <;> exact_mod_cast h

theorem value_positiveSub (a b : Code) :
    value (positiveSub a b) = max (value a-value b) 0 := by
  by_cases h : b.1*2^a.2 ≤ a.1*2^b.2
  · have hv : value b ≤ value a := (value_le_iff b a).mpr h
    rw [max_eq_left (sub_nonneg.mpr hv)]
    simp only [value,positiveSub,Nat.cast_sub h,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_add]
    field_simp
  · have hab : a.1*2^b.2 ≤ b.1*2^a.2 := by omega
    have hv : value a ≤ value b := (value_le_iff a b).mpr hab
    rw [max_eq_right (sub_nonpos.mpr hv)]
    simp [value,positiveSub,Nat.sub_eq_zero_of_le hab]

theorem value_minCode (a b : Code) : value (minCode a b) = min (value a) (value b) := by
  by_cases h : smaller a b
  · simp only [minCode,ite_eq_left h,min_eq_left ((value_le_iff a b).mpr h)]
  · have hv : value b ≤ value a := le_of_not_ge (fun hn => h ((value_le_iff a b).mp hn))
    simp only [minCode,ite_eq_right h,min_eq_right hv]

theorem value_maxCode (a b : Code) : value (maxCode a b) = max (value a) (value b) := by
  by_cases h : smaller a b
  · simp only [maxCode,ite_eq_left h,max_eq_right ((value_le_iff a b).mpr h)]
  · have hv : value b ≤ value a := le_of_not_ge (fun hn => h ((value_le_iff a b).mp hn))
    simp only [maxCode,ite_eq_right h,max_eq_left hv]

theorem value_shift (a : Code) (k : ℕ) : value (shift a k) = value a/(2:ℝ)^k := by
  simp only [value,shift,pow_add,div_div]

theorem value_interval (lo hi x : Code) : value (interval lo hi x) =
    max (max (value lo-value x) 0) (max (value x-value hi) 0) := by
  simp only [interval,value_maxCode,value_positiveSub]

theorem value_separator (g0 g1 : Code) (h0 : value g0 ≤ 1) :
    value (separator g0 g1) = 1/2+(value g1-value g0)/4 := by
  have hn := value_nonneg g1
  have hpos : 0 ≤ value (add two g1)-value g0 := by rw [value_add,value_two]; linarith
  rw [separator,value_shift,value_positiveSub,max_eq_left hpos,value_add,value_two]
  norm_num
  ring

theorem separator_range (g0 g1 : Code) (h0 : value g0 ≤ 1) (h1 : value g1 ≤ 1) :
    1/4 ≤ value (separator g0 g1) ∧ value (separator g0 g1) ≤ 3/4 := by
  rw [value_separator g0 g1 h0]
  have hn0 := value_nonneg g0
  have hn1 := value_nonneg g1
  constructor <;> linarith

theorem outputIndex_value (a : Code) :
    ((Rationals.q (outputIndex a) : ℚ) : ℝ) = value a :=
  Rationals.q_dyadicIndex_real a.1 a.2

private theorem pow_primrec : Primrec₂ (fun a b : ℕ => a^b) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem add_primrec : Primrec₂ add := by
  have ha : Primrec (fun a : Code × Code => a.1.1*2^a.2.2) :=
    Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst)
      (pow_primrec.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))
  have hb : Primrec (fun a : Code × Code => a.2.1*2^a.1.2) :=
    Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd)
      (pow_primrec.comp (Primrec.const 2) (Primrec.snd.comp Primrec.fst))
  exact (Primrec.pair (Primrec.nat_add.comp ha hb)
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂

theorem positiveSub_primrec : Primrec₂ positiveSub := by
  have ha : Primrec (fun a : Code × Code => a.1.1*2^a.2.2) :=
    Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst)
      (pow_primrec.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))
  have hb : Primrec (fun a : Code × Code => a.2.1*2^a.1.2) :=
    Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd)
      (pow_primrec.comp (Primrec.const 2) (Primrec.snd.comp Primrec.fst))
  exact (Primrec.pair (Primrec.nat_sub.comp ha hb)
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂

theorem smaller_primrec : PrimrecRel smaller :=
  Primrec.nat_le.comp
    (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst)
      (pow_primrec.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)))
    (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd)
      (pow_primrec.comp (Primrec.const 2) (Primrec.snd.comp Primrec.fst)))

theorem minCode_primrec : Primrec₂ minCode := Primrec.ite smaller_primrec Primrec.fst Primrec.snd

theorem maxCode_primrec : Primrec₂ maxCode := Primrec.ite smaller_primrec Primrec.snd Primrec.fst

theorem shift_primrec : Primrec₂ shift :=
  Primrec.pair (Primrec.fst.comp Primrec.fst)
    (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)

theorem interval_primrec :
    Primrec (fun a : (Code × Code) × Code => interval a.1.1 a.1.2 a.2) :=
  maxCode_primrec.comp
    (positiveSub_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
    (positiveSub_primrec.comp Primrec.snd (Primrec.snd.comp Primrec.fst))

theorem separator_primrec : Primrec₂ separator :=
  shift_primrec.comp (positiveSub_primrec.comp
    (add_primrec.comp (Primrec.const two) Primrec.snd) Primrec.fst) (Primrec.const 2)

theorem outputIndex_primrec : Primrec outputIndex :=
  Rationals.dyadicIndex_primrec

end CategoricalEssentialIncompleteness.V46.Miller.Cut.Dyadic
