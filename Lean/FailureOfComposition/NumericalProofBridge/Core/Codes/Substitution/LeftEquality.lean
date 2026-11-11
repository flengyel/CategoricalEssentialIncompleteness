/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProofBridge.Core.Codes.Substitution.LeftTemplate

/-! # Normalization of the left equality component -/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalProofBridge

open ProofSearch ConcreteEvaluator

theorem equalityLeftBody_eq (q r : ℕ) :
    equalityLeftBody q r =
      equalityBinderRew ▹ (firstSuccessGraph q).val := by
  calc
    equalityLeftBody q r =
        equalityBinderRew ▹ equalityLeftSpecialized q :=
      equalityLeftBody_eq_specialized q r
    _ = equalityBinderRew ▹ (firstSuccessGraph q).val := by
      rw [firstSuccessGraph_val_eq_specialized]

end FailureOfComposition.NumericalProofBridge
