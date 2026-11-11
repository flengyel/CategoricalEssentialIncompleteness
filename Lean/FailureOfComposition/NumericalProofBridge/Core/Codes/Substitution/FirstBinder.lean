/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProofBridge.Core.Codes.Substitution.EqualityPieces

/-! # First numeral under the two graph binders -/

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

theorem firstNumeralUnderTwoBinders_eq
    (phi : ArithmeticSemisentence 3) (q : ℕ) :
    (Rew.subst ![
      (↑q : ArithmeticSemiterm Empty 2),
      (#1 : ArithmeticSemiterm Empty 2),
      (#0 : ArithmeticSemiterm Empty 2)]) ▹ phi =
      (Rew.subst ![
        (#1 : ArithmeticSemiterm Empty 2),
        (#0 : ArithmeticSemiterm Empty 2)]) ▹
          (phi/[
            (↑q : ArithmeticSemiterm Empty 2),
            (#0 : ArithmeticSemiterm Empty 2),
            (#1 : ArithmeticSemiterm Empty 2)]) := by
  have hrew :
      Rew.subst ![
        (↑q : ArithmeticSemiterm Empty 2),
        (#1 : ArithmeticSemiterm Empty 2),
        (#0 : ArithmeticSemiterm Empty 2)] =
      (Rew.subst ![
        (#1 : ArithmeticSemiterm Empty 2),
        (#0 : ArithmeticSemiterm Empty 2)]).comp
          (Rew.subst ![
            (↑q : ArithmeticSemiterm Empty 2),
            (#0 : ArithmeticSemiterm Empty 2),
            (#1 : ArithmeticSemiterm Empty 2)]) := by
    ext i <;> fin_cases i <;> simp [Rew.comp_app]
  rw [hrew, TransitiveRewriting.comp_app]

end FailureOfComposition.NumericalProofBridge
