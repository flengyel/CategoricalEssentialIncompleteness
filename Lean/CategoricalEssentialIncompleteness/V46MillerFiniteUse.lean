/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerOracleProgramTable

/-! # Actual oracle programs for ordinary finite-use algorithms

The algorithm may return different numbers from different representations.
This construction supplies a single actual program and asserts no semantic
representation independence of those numbers.
-/

@[expose] public section
noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller.FiniteUse
open OracleProgram
open CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

/-- Wait for the specified use and then compute from exactly that prefix. -/
def table (N : ℕ → ℕ) (A : List ℕ × ℕ → ℕ) (a : List ℕ × ℕ) : Part ℕ :=
  if N a.2 ≤ a.1.length then Part.some (A (a.1.take (N a.2),a.2)) else Part.none

theorem table_partrec (N : ℕ → ℕ) (A : List ℕ × ℕ → ℕ)
    (hN : Computable N) (hA : Computable A) : Partrec (table N A) := by
  have hle : Computable (fun a : ℕ × ℕ => decide (a.1 ≤ a.2)) :=
    (show PrimrecPred (fun a : ℕ × ℕ => a.1 ≤ a.2) from Primrec.nat_le).computablePred.decide
  have hc : Computable (fun a : List ℕ × ℕ => decide (N a.2 ≤ a.1.length)) :=
    hle.comp (Computable.pair (hN.comp Computable.snd)
      (Computable.list_length.comp Computable.fst))
  have ha : Computable (fun a : List ℕ × ℕ => A (a.1.take (N a.2),a.2)) :=
    hA.comp (Computable.pair
      (Primrec.list_take.to_comp.comp (hN.comp Computable.snd) Computable.fst)
      Computable.snd)
  exact (Partrec.cond hc ha.partrec Partrec.none).of_eq (fun a => by
    simp only [table,Bool.cond_decide,PFun.coe_val])

theorem table_mem (N : ℕ → ℕ) (A : List ℕ × ℕ → ℕ) (l : List ℕ) (n y : ℕ) :
    y ∈ table N A (l,n) ↔ N n ≤ l.length ∧ y=A (l.take (N n),n) := by
  by_cases h : N n ≤ l.length <;> simp [table,h]

theorem table_monotone (N : ℕ → ℕ) (A : List ℕ × ℕ → ℕ) :
    MonotoneValues (table N A) := by
  intro l l' hl n y hy
  obtain ⟨hn,hy⟩ := (table_mem N A l n y).mp hy
  apply (table_mem N A l' n y).mpr
  refine ⟨hn.trans hl.length_le,?_⟩
  obtain ⟨t,rfl⟩ := hl
  rw [List.take_append_of_le_length hn]
  exact hy

theorem table_at_use (N : ℕ → ℕ) (A : List ℕ × ℕ → ℕ) (p : Bits) (n : ℕ) :
    table N A (numericalPrefix p (N n),n) = Part.some (A (numericalPrefix p (N n),n)) := by
  have ht : (numericalPrefix p (N n)).take (N n) = numericalPrefix p (N n) :=
    List.take_of_length_le (by simp)
  simp [table,ht]

/-- The index is selected before every oracle and input. Its numeric outputs
need not agree between representations of one real sequence. -/
theorem exists_program (N : ℕ → ℕ) (A : List ℕ × ℕ → ℕ)
    (hN : Computable N) (hA : Computable A) :
    ∃ d : ℕ,∀ p : Bits,∀ n : ℕ,
      numberedEval d p n = Part.some (A (numericalPrefix p (N n),n)) := by
  obtain ⟨d,hd⟩ := exists_uniform_index (table N A) (table_partrec N A hN hA) (table_monotone N A)
  refine ⟨d,?_⟩
  intro p n
  apply Part.eq_some_iff.mpr
  apply (hd p n (A (numericalPrefix p (N n),n))).mpr
  refine ⟨N n,?_⟩
  rw [table_at_use]
  exact Part.mem_some _

end CategoricalEssentialIncompleteness.V46.Miller.FiniteUse
