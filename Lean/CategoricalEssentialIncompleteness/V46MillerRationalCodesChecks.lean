/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRationalCodes


/-! # Statement checks in `V46MillerRationalCodesChecks` -/

@[expose] public section
namespace CategoricalEssentialIncompleteness.V46.Miller.Rationals.Checks
example : Function.Surjective q := q_surjective
example (r : ℚ) : q (rationalIndex r)=r := q_rationalIndex r
example (a d : ℕ) (hd : 0<d) : q (positiveIndex a d)=(a : ℚ)/(d : ℚ) := q_positiveIndex a d hd
example : Primrec₂ positiveIndex := positiveIndex_primrec
example : Primrec₂ dyadicIndex := dyadicIndex_primrec
example (a k : ℕ) : q (dyadicIndex a k)=(a : ℚ)/(2 : ℚ)^k := q_dyadicIndex a k
example (a k : ℕ) : ((q (dyadicIndex a k) : ℚ) : ℝ)=(a : ℝ)/(2 : ℝ)^k := q_dyadicIndex_real a k
end CategoricalEssentialIncompleteness.V46.Miller.Rationals.Checks
