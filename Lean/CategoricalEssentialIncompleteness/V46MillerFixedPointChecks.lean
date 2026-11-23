/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerFixedPoint

/-! # Statements for the existence of a Miller sequence -/

@[expose] public section
namespace CategoricalEssentialIncompleteness.V46.Miller.Checks
open Set

example (d : ℕ) :
    IsClosed {z : Bits × Set.Icc (0 : ℝ) 1 | z.2 ∈ nameInterval d z.1} :=
  nameInterval_graph_closed d

example (d : ℕ) (p : Bits) : ∃ l u : Set.Icc (0 : ℝ) 1,
    l ≤ u ∧ nameInterval d p = Set.Icc l u := nameInterval_box d p

example (d : ℕ) (p : Bits) (r : Set.Icc (0 : ℝ) 1)
    (h : ∀ k : ℕ, ∃ i, i ∈ OracleProgram.numberedEval d p k ∧
      |(Rationals.q i : ℝ) - (r : ℝ)| < ((2 : ℝ)^k)⁻¹) :
    nameInterval d p = {r} := nameInterval_singleton h

example (d : ℕ) :
    IsClosed {z : Point × Set.Icc (0 : ℝ) 1 | z.2 ∈ coordinateInterval d z.1} :=
  coordinateInterval_graph_closed d

example (d : ℕ) (z : Point) : ∃ l u : Set.Icc (0 : ℝ) 1,
    l ≤ u ∧ coordinateInterval d z = Set.Icc l u := coordinateInterval_box d z

example (d : ℕ) (z : Point) (r : Set.Icc (0 : ℝ) 1)
    (h : ∀ p : Bits, rho p = z → ∀ k : ℕ, ∃ i,
      i ∈ OracleProgram.numberedEval d p k ∧ |(Rationals.q i : ℝ) - (r : ℝ)| < ((2 : ℝ)^k)⁻¹) :
    coordinateInterval d z = {r} := coordinateInterval_singleton h

example (J : ℕ → Point → Set (Set.Icc (0 : ℝ) 1))
    (hc : ∀ d, IsClosed {z : Point × Set.Icc (0 : ℝ) 1 | z.2 ∈ J d z.1})
    (hi : ∀ d z, ∃ l u : Set.Icc (0 : ℝ) 1, l ≤ u ∧ J d z = Set.Icc l u) :
    ∃ a : Point, ∀ d, a d ∈ J d a := exists_coordinate_fixedPoint J hc hi

example : ∃ a : ℕ → Set.Icc (0 : ℝ) 1, ∀ d : ℕ, ∀ r : Set.Icc (0 : ℝ) 1,
    (∀ p : ℕ → Fin 2, rho p = a → ∀ k : ℕ, ∃ i : ℕ,
      i ∈ OracleProgram.numberedEval d p k ∧ |(Rationals.q i : ℝ) - (r : ℝ)| < ((2 : ℝ)^k)⁻¹) →
    a d = r := exists_isMiller

end CategoricalEssentialIncompleteness.V46.Miller.Checks
