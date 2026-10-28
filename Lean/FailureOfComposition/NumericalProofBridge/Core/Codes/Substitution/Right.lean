/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalProofBridge.Core.Codes.Substitution.Left

/-!
# Eventual-graph sentence substitution

This layer identifies the fixed right template with a closed eventual-graph instance.
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

private theorem rightSentenceTemplate_first_subst (r : ℕ) :
    (rightSentenceTemplate/[
      (↑r : ArithmeticSemiterm Empty 2),
      (#0 : ArithmeticSemiterm Empty 2),
      (#1 : ArithmeticSemiterm Empty 2)] : ArithmeticSemisentence 2) =
      (eventualGraph r).val := by
  have hrew :
      ((Rew.subst ![
        (↑r : ArithmeticSemiterm Empty 2),
        (#0 : ArithmeticSemiterm Empty 2),
        (#1 : ArithmeticSemiterm Empty 2)]).q).comp
          (Rew.subst ![
            (#0 : ArithmeticSemiterm Empty 4),
            (#1 : ArithmeticSemiterm Empty 4),
            (#2 : ArithmeticSemiterm Empty 4),
            (#3 : ArithmeticSemiterm Empty 4)]) =
        Rew.subst ![
          (#0 : ArithmeticSemiterm Empty 3),
          (↑r : ArithmeticSemiterm Empty 3),
          (#1 : ArithmeticSemiterm Empty 3),
          (#2 : ArithmeticSemiterm Empty 3)] := by
    ext i <;> fin_cases i <;> simp [Rew.comp_app, Rew.q]
  simp only [rightSentenceTemplate, Rewriting.app_exs,
    ← TransitiveRewriting.comp_app]
  rw [hrew]
  exact (eventualGraph_val r).symm

theorem rightSentenceTemplate_subst (r n m : ℕ) :
    (rightSentenceTemplate/[
      (↑r : ArithmeticSemiterm Empty 0),
      (↑n : ArithmeticSemiterm Empty 0),
      (↑m : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) =
      (eventualGraph r).val/[n, m] := by
  calc
    _ = ((rightSentenceTemplate/[
          (↑r : ArithmeticSemiterm Empty 2),
          (#0 : ArithmeticSemiterm Empty 2),
          (#1 : ArithmeticSemiterm Empty 2)] :
            ArithmeticSemisentence 2)/[
              (↑n : ArithmeticSemiterm Empty 0),
              (↑m : ArithmeticSemiterm Empty 0)] :
                ArithmeticSentence) :=
      substThreeNumerals_assoc rightSentenceTemplate r n m
    _ = (eventualGraph r).val/[n, m] := by
      rw [rightSentenceTemplate_first_subst]

end FailureOfComposition.NumericalProofBridge
