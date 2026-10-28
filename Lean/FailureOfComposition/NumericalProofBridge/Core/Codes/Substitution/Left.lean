/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalProofBridge.Core.Codes.Substitution.Equality

/-!
# First-success sentence substitution

This layer identifies the fixed left template with a closed first-success graph instance.
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

theorem leftSentenceTemplate_subst (q n m : ℕ) :
    (leftSentenceTemplate/[
      (↑q : ArithmeticSemiterm Empty 0),
      (↑n : ArithmeticSemiterm Empty 0),
      (↑m : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) =
      (firstSuccessGraph q).val/[n, m] := by
  simpa [leftSentenceTemplate, firstSuccessGraph] using
    substThreeNumerals_assoc canonicalPartrecGraphFormula.val q n m

end FailureOfComposition.NumericalProofBridge
