/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerStrictRationalCuts


/-! # Strict lower and upper rational cuts -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller.StrictRational

example (j number precision : ℕ) :
    ((Nat.unpair j).1%2≠0 ∨
      (Nat.unpair j).1/2*2^precision < number*((Nat.unpair j).2+1)) ↔
      (Rationals.q j : ℝ) < (number : ℝ)/(2 : ℝ)^precision :=
  belowTest_iff j number precision

example (j number precision : ℕ) :
    ((Nat.unpair j).1%2=0 ∧
      (number+1)*((Nat.unpair j).2+1) < (Nat.unpair j).1/2*2^precision) ↔
      ((number : ℝ)+1)/(2 : ℝ)^precision < (Rationals.q j : ℝ) :=
  aboveTest_iff j number precision

example (above : Bool) : PrimrecPred (Certificate above) := certificate_primrec above
example (above : Bool) : REPred (tableCertificate above) := tableCertificate_re above

example (above : Bool) (n j : ℕ) {s t : List ℕ} (hst : s<+:t) :
    tableCertificate above ((n,j),s) → tableCertificate above ((n,j),t) :=
  tableCertificate_mono above n j hst

example (a : Point) : Uniform.Enumerable (Uniform.Family.ofPoint a)
    (fun x : ℕ × ℕ => (Rationals.q x.2 : ℝ) < (a x.1 : ℝ)) :=
  rational_below_enumerable a

example (a : Point) : Uniform.Enumerable (Uniform.Family.ofPoint a)
    (fun x : ℕ × ℕ => (a x.1 : ℝ) < (Rationals.q x.2 : ℝ)) :=
  rational_above_enumerable a

example (a : Point) (n j : ℕ) (hj : (Rationals.q j : ℝ)<0) :
    (Rationals.q j : ℝ)<(a n : ℝ) := negative_below a n j hj

example (a : Point) (n j : ℕ) (hj : 1<(Rationals.q j : ℝ)) :
    (a n : ℝ)<(Rationals.q j : ℝ) := beyond_one_above a n j hj

example (a : Point) (n : ℕ) :
    ¬(a n : ℝ)<(Rationals.q (Rationals.dyadicIndex 0 0) : ℝ) := not_above_zero a n

example (a : Point) (n : ℕ) :
    ¬(Rationals.q (Rationals.dyadicIndex 1 0) : ℝ)<(a n : ℝ) := not_below_one a n

example : ∃ d : ℕ,∀ a : Point,∀ p∈representations a,∀ n j value : ℕ,
    value ∈ OracleProgram.numberedEval d p (Nat.pair n j) ↔
      (Rationals.q j : ℝ) < (a n : ℝ) ∧ value=0 :=
  exists_program_on_representations false

example : ∃ d : ℕ,∀ a : Point,∀ p∈representations a,∀ n j value : ℕ,
    value ∈ OracleProgram.numberedEval d p (Nat.pair n j) ↔
      (a n : ℝ) < (Rationals.q j : ℝ) ∧ value=0 :=
  exists_program_on_representations true

end CategoricalEssentialIncompleteness.V46.Miller.StrictRational
