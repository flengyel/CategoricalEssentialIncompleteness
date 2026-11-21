/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerFiniteUse


/-! # Oracle programs for ordinary finite-use algorithms -/

@[expose] public section
namespace CategoricalEssentialIncompleteness.V46.Miller.FiniteUse.Checks
example (N : ℕ → ℕ) (A : List ℕ × ℕ → ℕ) (hN : Computable N) (hA : Computable A) :
    Partrec (table N A) := table_partrec N A hN hA
example (N : ℕ → ℕ) (A : List ℕ × ℕ → ℕ) :
    LocalConnectedness.OracleComputation.MonotoneValues (table N A) := table_monotone N A
example (N : ℕ → ℕ) (A : List ℕ × ℕ → ℕ) (hN : Computable N) (hA : Computable A) :
    ∃ d : ℕ,∀ p : Bits,∀ n : ℕ,
      OracleProgram.numberedEval d p n = Part.some (A (OracleProgram.numericalPrefix p (N n),n)) :=
  exists_program N A hN hA
end CategoricalEssentialIncompleteness.V46.Miller.FiniteUse.Checks
