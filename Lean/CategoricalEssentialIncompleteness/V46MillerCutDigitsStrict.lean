/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerCutDigits
import CategoricalEssentialIncompleteness.V46MillerDyadicEffective

/-! # Uniform finite certificates for the two strict coordinate cuts

These are the actual cut domains in the representation-independent source.
Their enumeration uses only finite dyadic inequalities and retains the
same numerical word for each representation.
-/
noncomputable section
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.V46.Miller.CutDigits

theorem lower_numeral_iff (b : Bits) :
    Real.ofDigits b < 1/2 ↔ ∃ k,2*(numeral b k+1) < 2^k := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one
      (show (0 : ℝ) < 1/2-Real.ofDigits b by linarith)
      (show (2 : ℝ)⁻¹ < 1 by norm_num)
    rw [inv_pow] at hk
    have hb := (numeral_bounds b k).1
    have hu : ((numeral b k : ℝ)+1)/(2 : ℝ)^k < 1/2 := by
      rw [add_div,one_div]
      linarith
    have hp : (0 : ℝ) < 2^k := by positivity
    have hn : (2 : ℝ)*((numeral b k : ℝ)+1) < (2 : ℝ)^k := by
      have hu' := (div_lt_iff₀ hp).mp hu
      nlinarith
    exact ⟨k,by exact_mod_cast hn⟩
  · rintro ⟨k,hk⟩
    have hn : (2 : ℝ)*((numeral b k : ℝ)+1) < (2 : ℝ)^k := by exact_mod_cast hk
    have hu : ((numeral b k : ℝ)+1)/(2 : ℝ)^k < 1/2 := by
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2^k)).mpr
      nlinarith
    exact (numeral_bounds b k).2.trans_lt hu

theorem upper_numeral_iff (b : Bits) :
    1/2 < Real.ofDigits b ↔ ∃ k,2^k < 2*numeral b k := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one
      (show (0 : ℝ) < Real.ofDigits b-1/2 by linarith)
      (show (2 : ℝ)⁻¹ < 1 by norm_num)
    rw [inv_pow] at hk
    have hb := (numeral_bounds b k).2
    rw [add_div,one_div] at hb
    have hl : (1 : ℝ)/2 < (numeral b k : ℝ)/(2 : ℝ)^k := by linarith
    have hn : (2 : ℝ)^k < 2*(numeral b k : ℝ) := by
      have hl' := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2^k)).mp hl
      nlinarith
    exact ⟨k,by exact_mod_cast hn⟩
  · rintro ⟨k,hk⟩
    have hn : (2 : ℝ)^k < 2*(numeral b k : ℝ) := by exact_mod_cast hk
    have hl : (1 : ℝ)/2 < (numeral b k : ℝ)/(2 : ℝ)^k := by
      apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2^k)).mpr
      nlinarith
    exact hl.trans_le (numeral_bounds b k).1

private theorem powTwo_primrec : Primrec (fun k : ℕ => 2^k) := by
  apply (Primrec.nat_rec₁ (1 : ℕ)
    (Primrec.nat_mul.comp Primrec.snd (Primrec.const 2)).to₂).of_eq
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simpa only [pow_succ] using congrArg (fun n => n*2) ih

def StrictSide (upper : Bool) (z : Point) (n : ℕ) : Prop :=
  if upper then 1/2 < (z n : ℝ) else (z n : ℝ) < 1/2

def Certificate (upper : Bool) (a : (Word × ℕ) × ℕ) : Prop :=
  Located a.1.1 a.1.2 a.2 ∧
    if upper then 2^a.2 < 2*wordNumeral a.1.1 a.1.2 a.2
      else 2*(wordNumeral a.1.1 a.1.2 a.2+1) < 2^a.2

theorem certificate_primrec (upper : Bool) : PrimrecPred (Certificate upper) := by
  have hn := wordNumeral_primrec
  have hp := powTwo_primrec.comp (Primrec.snd (α := Word × ℕ))
  cases upper
  · exact located_primrec.and (Primrec.nat_lt.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_add.comp hn (Primrec.const 1))) hp)
  · exact located_primrec.and (Primrec.nat_lt.comp hp
      (Primrec.nat_mul.comp (Primrec.const 2) hn))

theorem certificate_mono (upper : Bool) {u v : Word} (h : u <+: v) (n k : ℕ)
    (hc : Certificate upper ((u,n),k)) : Certificate upper ((v,n),k) := by
  obtain ⟨t,rfl⟩ := h
  refine ⟨?_,?_⟩
  · intro j hj
    have hh : Nat.pair n j<u.length := hc.1 j hj
    change Nat.pair n j<(u++t).length
    rw [List.length_append]
    omega
  · simpa only [wordNumeral_append u t n k hc.1] using hc.2

theorem certificate_prefix_iff (upper : Bool) (p : Bits) (n : ℕ) :
    StrictSide upper (rho p) n ↔
      ∃ N k,Certificate upper ((bitPrefix p N,n),k) := by
  cases upper
  · change Real.ofDigits (fun j => p (Nat.pair n j)) < 1/2 ↔ _
    rw [lower_numeral_iff]
    constructor
    · rintro ⟨k,hk⟩
      refine ⟨queryBound n k,k,located_prefix p n k,?_⟩
      change 2*(wordNumeral (bitPrefix p (queryBound n k)) n k+1)<2^k
      rw [wordNumeral_prefix p _ n k (query_lt_bound n k)]
      exact hk
    · rintro ⟨N,k,hl,hk⟩
      refine ⟨k,?_⟩
      change 2*(wordNumeral (bitPrefix p N) n k+1)<2^k at hk
      simpa only [wordNumeral_prefix p N n k (fun j hj => by
        simpa only [prefix_length] using hl j hj)] using hk
  · change 1/2 < Real.ofDigits (fun j => p (Nat.pair n j)) ↔ _
    rw [upper_numeral_iff]
    constructor
    · rintro ⟨k,hk⟩
      refine ⟨queryBound n k,k,located_prefix p n k,?_⟩
      change 2^k<2*wordNumeral (bitPrefix p (queryBound n k)) n k
      rw [wordNumeral_prefix p _ n k (query_lt_bound n k)]
      exact hk
    · rintro ⟨N,k,hl,hk⟩
      refine ⟨k,?_⟩
      change 2^k<2*wordNumeral (bitPrefix p N) n k at hk
      simpa only [wordNumeral_prefix p N n k (fun j hj => by
        simpa only [prefix_length] using hl j hj)] using hk

theorem strictSide_enumerable (upper : Bool) (z : Point) :
    Uniform.Enumerable (Uniform.Family.ofPoint z) (StrictSide upper z) := by
  let Q : ℕ × List ℕ → Prop := fun a =>
    ∃ k,Certificate upper ((normalizeWord a.2,a.1),k)
  have hcert : REPred (fun a : (ℕ × List ℕ) × ℕ =>
      Certificate upper ((normalizeWord a.1.2,a.1.1),a.2)) :=
    REPred.comp (Computable.pair
      (Computable.pair (normalizeWord_primrec.to_comp.comp
        (Computable.snd.comp Computable.fst)) (Computable.fst.comp Computable.fst))
      Computable.snd) (certificate_primrec upper).computablePred.to_re
  refine ⟨Q,hcert.projection,?_,?_⟩
  · rintro n l l' h ⟨k,hk⟩
    exact ⟨k,certificate_mono upper (normalizeWord_prefix l l' h) n k hk⟩
  · intro p hp n
    have hz : rho p = z := hp
    constructor
    · intro h
      have hr : StrictSide upper (rho p) n := hz.symm ▸ h
      obtain ⟨N,k,hk⟩ := (certificate_prefix_iff upper p n).mp hr
      refine ⟨N,k,?_⟩
      simpa only [OracleProgram.numericalPrefix,normalizeWord_numericalPrefix] using hk
    · rintro ⟨N,k,hk⟩
      have hr : StrictSide upper (rho p) n :=
        (certificate_prefix_iff upper p n).mpr ⟨N,k,by
          simpa only [OracleProgram.numericalPrefix,normalizeWord_numericalPrefix] using hk⟩
      exact hz ▸ hr

theorem lowerCut_enumerable (z : Point) :
    Uniform.Enumerable (Uniform.Family.ofPoint z) (· ∈ lowerCut z) :=
  strictSide_enumerable false z

theorem upperCut_enumerable (z : Point) :
    Uniform.Enumerable (Uniform.Family.ofPoint z) (· ∈ upperCut z) :=
  strictSide_enumerable true z

def lowerIdem (z : Point) : Idem
    (Uniform.N (Uniform.Family.ofPoint z)) :=
  Uniform.setIdem (Uniform.N (Uniform.Family.ofPoint z)) (lowerCut z) (lowerCut_enumerable z)

def upperIdem (z : Point) : Idem
    (Uniform.N (Uniform.Family.ofPoint z)) :=
  Uniform.setIdem (Uniform.N (Uniform.Family.ofPoint z)) (upperCut z) (upperCut_enumerable z)

@[simp] theorem lowerIdem_support (z : Point) : Uniform.support (lowerIdem z) = lowerCut z :=
  Uniform.support_setIdem _ _ _

@[simp] theorem upperIdem_support (z : Point) : Uniform.support (upperIdem z) = upperCut z :=
  Uniform.support_setIdem _ _ _

end CategoricalEssentialIncompleteness.V46.Miller.CutDigits
