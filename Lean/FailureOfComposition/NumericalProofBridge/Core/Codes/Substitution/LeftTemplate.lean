/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalProofBridge.Core.Codes.Substitution.FirstSuccessValue

/-! # The directly constructed left equality component -/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalProofBridge

open ProofSearch ConcreteEvaluator

theorem equalityLeftBody_eq_specialized (q r : ℕ) :
    equalityLeftBody q r =
      equalityBinderRew ▹ equalityLeftSpecialized q := by
  simpa only [equalityLeftBody, equalityBinderRew,
    equalityLeftSpecialized] using
    firstNumeralUnderTwoBinders_eq canonicalPartrecGraphFormula.val q

end FailureOfComposition.NumericalProofBridge
