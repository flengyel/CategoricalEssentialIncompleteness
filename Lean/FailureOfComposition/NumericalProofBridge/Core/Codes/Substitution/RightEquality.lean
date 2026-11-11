/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProofBridge.Core.Codes.Substitution.LeftEquality

/-! # Normalization of the right equality component -/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.NumericalProofBridge

open ProofSearch ConcreteEvaluator
open FFL.FirstOrder.Arithmetic.Bootstrapping

theorem equalityRightBody_eq (q r : ℕ) :
    (∃¹ equalityRightOpen q r : ArithmeticSemisentence 2) =
      equalityBinderRew ▹
        (eventualGraph r).val := by
  have hopen : equalityRightOpen q r =
      equalityBinderRew.q ▹ equalityRightSpecialized r := by
    simpa only [equalityRightOpen, equalityBinderRew,
      equalityRightSpecialized] using
      secondNumeralUnderStageAndTwoBinders_eq
        (evalnCertificateFormula : ArithmeticSemisentence 4) r
  have hgraph : (eventualGraph r).val =
      (∃¹ equalityRightSpecialized r : ArithmeticSemisentence 2) := by
    simpa only [equalityRightSpecialized] using eventualGraph_val r
  calc
    (∃¹ equalityRightOpen q r : ArithmeticSemisentence 2) =
        ∃¹ (equalityBinderRew.q ▹ equalityRightSpecialized r) := by
      exact congrArg
        (fun phi : ArithmeticSemisentence 3 =>
          (∃¹ phi : ArithmeticSemisentence 2)) hopen
    _ = equalityBinderRew ▹
        (∃¹ equalityRightSpecialized r : ArithmeticSemisentence 2) := by
      rfl
    _ = equalityBinderRew ▹ (eventualGraph r).val := by
      rw [hgraph]

end FailureOfComposition.NumericalProofBridge
