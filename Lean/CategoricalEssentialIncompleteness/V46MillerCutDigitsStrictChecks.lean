/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutDigitsStrict


/-! # Statement checks in `V46MillerCutDigitsStrictChecks` -/

@[expose] public section
namespace CategoricalEssentialIncompleteness.V46.Miller.CutDigits.Checks

example (b : Bits) : Real.ofDigits b < 1/2 ↔ ∃ k,2*(numeral b k+1) < 2^k :=
  lower_numeral_iff b

example (b : Bits) : 1/2 < Real.ofDigits b ↔ ∃ k,2^k < 2*numeral b k :=
  upper_numeral_iff b

example (z : Point) :
    Uniform.Enumerable (Uniform.Family.ofPoint z) (fun n => (z n : ℝ) < 1/2) :=
  lowerCut_enumerable z

example (z : Point) :
    Uniform.Enumerable (Uniform.Family.ofPoint z) (fun n => 1/2 < (z n : ℝ)) :=
  upperCut_enumerable z

example (z : Point) : Uniform.support (lowerIdem z) = {n | (z n : ℝ) < 1/2} :=
  lowerIdem_support z

example (z : Point) : Uniform.support (upperIdem z) = {n | 1/2 < (z n : ℝ)} :=
  upperIdem_support z

end CategoricalEssentialIncompleteness.V46.Miller.CutDigits.Checks
