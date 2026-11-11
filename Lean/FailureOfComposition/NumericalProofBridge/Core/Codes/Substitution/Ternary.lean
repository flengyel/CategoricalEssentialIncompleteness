/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProofBridge.Core.Codes.Base

/-!
# Associativity of three-numeral substitution

This layer records the substitution identity shared by the closed graph instances.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open Arith.FixedFormulaNumeralSubstitution
open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.NumericalProofBridge

open ProofSearch ConcreteEvaluator
open FFL.FirstOrder.Arithmetic.Bootstrapping

theorem substThreeNumerals_assoc
    (phi : ArithmeticSemisentence 3) (a b c : ℕ) :
    (phi/[
      (↑a : ArithmeticSemiterm Empty 0),
      (↑b : ArithmeticSemiterm Empty 0),
      (↑c : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) =
      ((phi/[
        (↑a : ArithmeticSemiterm Empty 2),
        (#0 : ArithmeticSemiterm Empty 2),
        (#1 : ArithmeticSemiterm Empty 2)] : ArithmeticSemisentence 2)/[
          (↑b : ArithmeticSemiterm Empty 0),
          (↑c : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) := by
  have hrew :
      (Rew.subst ![
        (↑b : ArithmeticSemiterm Empty 0),
        (↑c : ArithmeticSemiterm Empty 0)]).comp
          (Rew.subst ![
            (↑a : ArithmeticSemiterm Empty 2),
            (#0 : ArithmeticSemiterm Empty 2),
            (#1 : ArithmeticSemiterm Empty 2)]) =
        Rew.subst ![
          (↑a : ArithmeticSemiterm Empty 0),
          (↑b : ArithmeticSemiterm Empty 0),
          (↑c : ArithmeticSemiterm Empty 0)] := by
    rw [Rew.subst_comp_subst]
    ext i <;> fin_cases i <;> simp [Function.comp_def]
  calc
    _ = ((Rew.subst ![
        (↑b : ArithmeticSemiterm Empty 0),
        (↑c : ArithmeticSemiterm Empty 0)]).comp
          (Rew.subst ![
            (↑a : ArithmeticSemiterm Empty 2),
            (#0 : ArithmeticSemiterm Empty 2),
            (#1 : ArithmeticSemiterm Empty 2)])) ▹ phi := by rw [hrew]
    _ = _ := by rw [TransitiveRewriting.comp_app]

end FailureOfComposition.NumericalProofBridge
