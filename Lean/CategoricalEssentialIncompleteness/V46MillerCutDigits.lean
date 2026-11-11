/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDyadicSeparation
public import CategoricalEssentialIncompleteness.V46MillerCategoryRelative

/-! # The actual first-digit separator of the two coordinate cuts

One fixed finite-table program reads the first binary digit of coordinate n.
Its output is total for every binary oracle. The decided set can depend on
the oracle at dyadic coordinates; no representation independence is imposed.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open Encodable

namespace CategoricalEssentialIncompleteness.V46.Miller.CutDigits

def lowerCut (z : Point) : Set ℕ := {n | (z n : ℝ) < 1/2}
def upperCut (z : Point) : Set ℕ := {n | 1/2 < (z n : ℝ)}

theorem head_bounds (b : Bits) :
    ((b 0).val : ℝ)/2 ≤ Real.ofDigits b ∧
      Real.ofDigits b ≤ (((b 0).val : ℝ)+1)/2 := by
  simpa only [numeral,Nat.mul_zero,Nat.zero_add,pow_one] using numeral_bounds b 1

theorem first_zero_of_lt (b : Bits) (h : Real.ofDigits b < 1/2) : b 0 = 0 := by
  apply Fin.ext
  by_contra hn
  have hv : (b 0).val = 1 := by have hb := (b 0).isLt; omega
  have hb := (head_bounds b).1
  rw [hv] at hb
  norm_num at hb
  linarith

theorem first_one_of_gt (b : Bits) (h : 1/2 < Real.ofDigits b) : b 0 = 1 := by
  apply Fin.ext
  by_contra hn
  have hv : (b 0).val = 0 := by have hb := (b 0).isLt; omega
  have hb := (head_bounds b).2
  rw [hv] at hb
  norm_num at hb
  linarith

theorem coordinate_first_zero (p : Bits) (n : ℕ) (h : n ∈ lowerCut (rho p)) :
    p (Nat.pair n 0) = 0 :=
  first_zero_of_lt (fun j => p (Nat.pair n j)) h

theorem coordinate_first_one (p : Bits) (n : ℕ) (h : n ∈ upperCut (rho p)) :
    p (Nat.pair n 0) = 1 :=
  first_one_of_gt (fun j => p (Nat.pair n j)) h

/-- The printed C_p, with the fixed recursive coordinate pairing. -/
def separator (p : Bits) : Set ℕ := {n | p (Nat.pair n 0) = 0}

theorem separates_rho (p : Bits) :
    lowerCut (rho p) ⊆ separator p ∧ Disjoint (separator p) (upperCut (rho p)) := by
  refine ⟨fun n hn => coordinate_first_zero p n hn,Set.disjoint_left.mpr ?_⟩
  intro n hn hr
  have h₀ : p (Nat.pair n 0) = 0 := hn
  have h₁ := coordinate_first_one p n hr
  have he : (0 : Fin 2) = 1 := h₀.symm.trans h₁
  exact (by decide : (0 : Fin 2) ≠ 1) he

theorem separates_point (z : Point) (p : Bits) (hp : p ∈ representations z) :
    lowerCut z ⊆ separator p ∧ Disjoint (separator p) (upperCut z) := by
  change rho p = z at hp
  simpa only [hp] using separates_rho p

def decision (p : Bits) (n : ℕ) : ℕ := 1-(p (Nat.pair n 0)).val

theorem decision_le_one (p : Bits) (n : ℕ) : decision p n ≤ 1 := Nat.sub_le ..

theorem decision_one_iff (p : Bits) (n : ℕ) : decision p n = 1 ↔ n ∈ separator p := by
  change 1-(p (Nat.pair n 0)).val = 1 ↔ p (Nat.pair n 0) = 0
  constructor
  · intro h
    apply Fin.ext
    omega
  · intro h
    rw [h]
    rfl

private def decisionTable (a : List ℕ × ℕ) : Part ℕ :=
  (OracleProgram.tableOracle a.1 (Nat.pair a.2 0)).map (fun b => 1-b)

private theorem decisionTable_partrec : Partrec decisionTable := by
  have hq : Computable (fun a : List ℕ × ℕ => Nat.pair a.2 0) :=
    Primrec₂.natPair.to_comp.comp Computable.snd (Computable.const 0)
  have hread : Partrec (fun a : List ℕ × ℕ =>
      OracleProgram.tableOracle a.1 (Nat.pair a.2 0)) :=
    (Computable.list_getElem?.comp Computable.fst hq).ofOption
  exact hread.map ((Primrec.nat_sub.to_comp.comp (Computable.const 1)
    Computable.snd).to₂)

private theorem decisionTable_monotone : OracleComputation.MonotoneValues decisionTable := by
  intro l l' h n y hy
  obtain ⟨b,hb,hby⟩ := (Part.mem_map_iff _).mp hy
  exact (Part.mem_map_iff _).mpr
    ⟨b,OracleProgram.tableOracle_mono h (Nat.pair n 0) b hb,hby⟩

/-- This one ordinary program index is chosen before every binary oracle. -/
@[no_expose] def decisionIndex : ℕ := encode (OracleProgram.ofTable decisionTable decisionTable_partrec)

theorem decisionIndex_eval (p : Bits) (n : ℕ) :
    OracleProgram.numberedEval decisionIndex p n = Part.some (decision p n) := by
  apply Part.ext
  intro y
  rw [decisionIndex,OracleProgram.numberedEval_encode,
    OracleProgram.ofTable_graph decisionTable decisionTable_partrec decisionTable_monotone]
  constructor
  · rintro ⟨k,hk⟩
    obtain ⟨b,hb,he⟩ := (Part.mem_map_iff _).mp hk
    have hbit := OracleProgram.tableOracle_prefix p k (Nat.pair n 0) b hb
    have hb' : b = (p (Nat.pair n 0)).val := Part.mem_some_iff.mp hbit
    exact Part.mem_some_iff.mpr (by simpa only [decision,hb'] using he.symm)
  · intro hy
    refine ⟨Nat.pair n 0+1,(Part.mem_map_iff _).mpr ?_⟩
    refine ⟨(p (Nat.pair n 0)).val,?_,?_⟩
    · simp only [OracleProgram.tableOracle,
        OracleProgram.numericalPrefix_getElem? p (Nat.pair n 0+1) (Nat.pair n 0)
          (Nat.lt_succ_self _),Part.coe_some]
      exact Part.mem_some _
    · exact (Part.mem_some_iff.mp hy).symm

/-- Fixed-p recursiveness follows from the actual full oracle-machine
comparison, and concerns the numerical VALUE as well as totality. -/
theorem decision_recursiveIn (p : Bits) :
    Nat.RecursiveIn (OracleComputation.oracleSet (OracleRelative.oracleSupport p))
      (fun n => Part.some (decision p n)) :=
  (OracleRelative.numberedEval_recursiveIn decisionIndex p).of_eq (decisionIndex_eval p)

theorem uniform_recursive_separator :
    ∃ e : ℕ,∀ p : Bits,∀ n,
      OracleProgram.numberedEval e p n = Part.some (decision p n) ∧
        (decision p n = 1 ↔ n ∈ separator p) :=
  ⟨decisionIndex,fun p n => ⟨decisionIndex_eval p n,decision_one_iff p n⟩⟩

theorem fixed_representation_separator (z : Point) (p : Bits) (hp : p ∈ representations z) :
    lowerCut z ⊆ separator p ∧ Disjoint (separator p) (upperCut z) ∧
      Nat.RecursiveIn (OracleComputation.oracleSet (OracleRelative.oracleSupport p))
        (fun n => Part.some (decision p n)) :=
  ⟨(separates_point z p hp).1,(separates_point z p hp).2,decision_recursiveIn p⟩

end CategoricalEssentialIncompleteness.V46.Miller.CutDigits
