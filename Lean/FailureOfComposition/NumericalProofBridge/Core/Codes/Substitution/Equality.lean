/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalProofBridge.Core.Codes.Substitution.TemplateDirect

/-!
# Uniform-equality sentence substitution

This layer identifies the fixed equality template with its uniform graph sentence.
-/

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

theorem equalitySentenceTemplate_subst (q r : ℕ) :
    (equalitySentenceTemplate/[
      (↑q : ArithmeticSemiterm Empty 0),
      (↑r : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) =
      uniformSentence (firstSuccessGraph q) (eventualGraph r) := by
  exact (equalitySentenceTemplate_subst_eq_direct q r).trans
    (directEqualitySentence_eq q r)

end FailureOfComposition.NumericalProofBridge
