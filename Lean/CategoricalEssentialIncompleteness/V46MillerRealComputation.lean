/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRationalCodes
public import CategoricalEssentialIncompleteness.V46MillerOracleProgramEffective

/-! # Real computation and the Miller property

An oracle computes a real by producing rational approximations. Rational
indices may differ across representations. Ordinary oracle specialization
then yields the coordinate equation required by the cut reduction. This
module supplies no separating-real approximation algorithm.
-/

@[expose] public section
noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller
open OracleProgram

/-- Total numerical approximation, with the manuscript's strict error bound. -/
def ComputesReal (d : ℕ) (p : Bits) (r : ℝ) : Prop :=
  ∀ k : ℕ,∃ i : ℕ,i ∈ numberedEval d p k ∧
    |(Rationals.q i : ℝ)-r| < ((2 : ℝ)^k)⁻¹

/-- The Miller property for the fixed acceptable machine/rational enumerations. -/
def IsMiller (a : Point) : Prop :=
  ∀ d : ℕ,∀ r : Set.Icc (0 : ℝ) 1,
    (∀ p ∈ representations a,ComputesReal d p (r : ℝ)) → a d=r

theorem specializes_computesReal (d x : ℕ) (p : Bits) (r : ℝ)
    (h : ∀ k : ℕ,∃ i : ℕ,i ∈ numberedEval d p (Nat.pair x k) ∧
      |(Rationals.q i : ℝ)-r| < ((2 : ℝ)^k)⁻¹) :
    ComputesReal (specializationIndex d x) p r := by
  intro k
  simpa only [specializationIndex_eval] using h k

theorem specializedIndex_computable (d : ℕ) : Computable (specializationIndex d) :=
  specializationIndex_computable.comp (Computable.const d) Computable.id

/-- Apply the Miller property after the approximation program is proved. The approximation
premise is discharged by the concrete geometry/series code in the cut-reduction
application, not added to its hypotheses. -/
theorem miller_coordinate_of_approximation
    (a : Point) (ha : IsMiller a) (d : ℕ)
    (R : ℕ → Point → Set.Icc (0 : ℝ) 1)
    (h : ∀ p : Bits,∀ e k : ℕ,∃ i : ℕ,
      i ∈ numberedEval d p (Nat.pair e k) ∧
        |(Rationals.q i : ℝ)-(R e (rho p) : ℝ)| < ((2 : ℝ)^k)⁻¹) :
    ∀ e : ℕ,a (specializationIndex d e)=R e a := by
  intro e
  apply ha (specializationIndex d e) (R e a)
  intro p hp
  have he : rho p=a := hp
  apply specializes_computesReal d e p (R e a)
  intro k
  simpa only [he] using h p e k

end CategoricalEssentialIncompleteness.V46.Miller
