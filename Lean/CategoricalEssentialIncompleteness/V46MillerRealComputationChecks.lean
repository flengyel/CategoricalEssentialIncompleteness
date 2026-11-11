/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRealComputation


/-! # Statement checks in `V46MillerRealComputationChecks` -/

@[expose] public section
namespace CategoricalEssentialIncompleteness.V46.Miller.Checks
example (d : ℕ) (p : Bits) (r : ℝ) :
    ComputesReal d p r ↔ ∀ k : ℕ,∃ i : ℕ,i ∈ OracleProgram.numberedEval d p k ∧
      |(Rationals.q i : ℝ)-r| < ((2 : ℝ)^k)⁻¹ := Iff.rfl
example (a : Point) :
    IsMiller a ↔ ∀ d : ℕ,∀ r : Set.Icc (0 : ℝ) 1,
      (∀ p ∈ representations a,ComputesReal d p (r : ℝ)) → a d=r := Iff.rfl
example (d : ℕ) : Computable (OracleProgram.specializationIndex d) := specializedIndex_computable d
example (a : Point) (ha : IsMiller a) (d : ℕ)
    (R : ℕ → Point → Set.Icc (0 : ℝ) 1)
    (h : ∀ p : Bits,∀ e k : ℕ,∃ i : ℕ,
      i ∈ OracleProgram.numberedEval d p (Nat.pair e k) ∧
        |(Rationals.q i : ℝ)-(R e (rho p) : ℝ)| < ((2 : ℝ)^k)⁻¹) :
    ∀ e : ℕ,a (OracleProgram.specializationIndex d e)=R e a :=
  miller_coordinate_of_approximation a ha d R h
end CategoricalEssentialIncompleteness.V46.Miller.Checks
