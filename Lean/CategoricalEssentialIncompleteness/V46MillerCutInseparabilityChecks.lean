/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutInseparability


/-! # Statement checks in `V46MillerCutInseparabilityChecks` -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.Miller.CutInseparability.Checks

example (z : Point) : Inseparable (diagonal0 z) (diagonal1 z) := source_diagonal_inseparable z

example (z : Point) (e : ℕ) : e ∈ Uniform.support (diagonal0 z) ↔
    ∃ m,(∀ p ∈ representations z,m ∈ OracleProgram.numberedEval e p e) ∧ m%2=0 := by
  simp only [diagonal0_support,Unanimity.tau_graph]

example (z : Point) (e : ℕ) : e ∈ Uniform.support (diagonal1 z) ↔
    ∃ m,(∀ p ∈ representations z,m ∈ OracleProgram.numberedEval e p e) ∧ m%2=1 := by
  simp only [diagonal1_support,Unanimity.tau_graph]

example (z : Point) (h : ℕ → ℕ) (hh : Computable h)
    (h₀ : h ⁻¹' {n | (z n : ℝ) < 1/2} = Uniform.support (diagonal0 z))
    (h₁ : h ⁻¹' {n | 1/2 < (z n : ℝ)} = Uniform.support (diagonal1 z)) :
    Inseparable (CutDigits.lowerIdem z) (CutDigits.upperIdem z) :=
  cuts_inseparable_of_recursive_reduction z h hh h₀ h₁

example (z : Point) (h : ℕ → ℕ) (hh : Computable h)
    (h₀ : h ⁻¹' CutDigits.lowerCut z = Uniform.support (diagonal0 z))
    (h₁ : h ⁻¹' CutDigits.upperCut z = Uniform.support (diagonal1 z))
    (p : Bits) (hp : p ∈ representations z) :
    Uniform.support (diagonal0 z) ⊆ h ⁻¹' {n | p (Nat.pair n 0) = 0} ∧
      Disjoint (h ⁻¹' {n | p (Nat.pair n 0) = 0}) (Uniform.support (diagonal1 z)) ∧
      Nat.RecursiveIn (OracleComputation.oracleSet (OracleRelative.oracleSupport p))
        (fun e => Part.some (1-(p (Nat.pair (h e) 0)).val)) :=
  diagonal_fixed_separator_of_recursive_reduction z h hh h₀ h₁ p hp

end CategoricalEssentialIncompleteness.V46.Miller.CutInseparability.Checks
