/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProofBridge.Core.Codes.Substitution.SecondBinder

/-! # The specialized first-success graph value -/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalProofBridge

open ProofSearch ConcreteEvaluator

theorem firstSuccessGraph_val_eq_specialized (q : ℕ) :
    (firstSuccessGraph q).val = equalityLeftSpecialized q := by
  simpa only [equalityLeftSpecialized] using firstSuccessGraph_val q

end FailureOfComposition.NumericalProofBridge
