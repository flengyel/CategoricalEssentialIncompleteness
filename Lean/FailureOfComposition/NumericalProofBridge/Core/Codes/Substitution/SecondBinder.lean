/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProofBridge.Core.Codes.Substitution.FirstBinder

/-! # Second numeral under a stage binder and two graph binders -/

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

theorem secondNumeralUnderStageAndTwoBinders_eq
    (phi : ArithmeticSemisentence 4) (r : ℕ) :
    (Rew.subst ![
      (#0 : ArithmeticSemiterm Empty 3),
      (↑r : ArithmeticSemiterm Empty 3),
      (#2 : ArithmeticSemiterm Empty 3),
      (#1 : ArithmeticSemiterm Empty 3)]) ▹ phi =
      ((Rew.subst ![
        (#1 : ArithmeticSemiterm Empty 2),
        (#0 : ArithmeticSemiterm Empty 2)]).q) ▹
          (phi/[
            (#0 : ArithmeticSemiterm Empty 3),
            (↑r : ArithmeticSemiterm Empty 3),
            (#1 : ArithmeticSemiterm Empty 3),
            (#2 : ArithmeticSemiterm Empty 3)]) := by
  have hrew :
      Rew.subst ![
        (#0 : ArithmeticSemiterm Empty 3),
        (↑r : ArithmeticSemiterm Empty 3),
        (#2 : ArithmeticSemiterm Empty 3),
        (#1 : ArithmeticSemiterm Empty 3)] =
      ((Rew.subst ![
        (#1 : ArithmeticSemiterm Empty 2),
        (#0 : ArithmeticSemiterm Empty 2)]).q).comp
          (Rew.subst ![
            (#0 : ArithmeticSemiterm Empty 3),
            (↑r : ArithmeticSemiterm Empty 3),
            (#1 : ArithmeticSemiterm Empty 3),
            (#2 : ArithmeticSemiterm Empty 3)]) := by
    ext i <;> fin_cases i <;> simp [Rew.comp_app, Rew.q]
  rw [hrew, TransitiveRewriting.comp_app]

end FailureOfComposition.NumericalProofBridge
