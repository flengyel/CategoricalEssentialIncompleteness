/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProofBridge.Core.Codes.Substitution.RightEquality

/-! # Direct and semantic uniform-equality sentences -/

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

private theorem quantifiedIff_congr
    {left₁ left₂ right₁ right₂ : ArithmeticSemisentence 2}
    (hleft : left₁ = left₂) (hright : right₁ = right₂) :
    (∀¹ ∀¹ LogicalConnective.iff left₁ right₁ : ArithmeticSentence) =
      ∀¹ ∀¹ LogicalConnective.iff left₂ right₂ := by
  exact congrArg
    (fun phi : ArithmeticSemisentence 2 =>
      (∀¹ ∀¹ phi : ArithmeticSentence))
    (congrArg₂
      (fun phi psi : ArithmeticSemisentence 2 =>
        LogicalConnective.iff phi psi) hleft hright)

theorem directEqualitySentence_eq (q r : ℕ) :
    directEqualitySentence q r =
      uniformSentence (firstSuccessGraph q) (eventualGraph r) := by
  calc
    directEqualitySentence q r =
        ∀¹ ∀¹ LogicalConnective.iff
          (equalityLeftBody q r) (∃¹ equalityRightOpen q r) := rfl
    _ = ∀¹ ∀¹ LogicalConnective.iff
          (equalityBinderRew ▹ (firstSuccessGraph q).val)
          (equalityBinderRew ▹ (eventualGraph r).val) :=
      quantifiedIff_congr (equalityLeftBody_eq q r)
        (equalityRightBody_eq q r)
    _ = uniformSentence (firstSuccessGraph q) (eventualGraph r) := rfl

end FailureOfComposition.NumericalProofBridge
