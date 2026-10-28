/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalProofBridge.Core.Codes.Substitution.Ternary

/-!
# Components of the uniform-equality sentence

These named components support a branchwise primitive-recursiveness proof for
the uniform graph-comparison sentence.
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

def equalityBinderRew : Rew ℒₒᵣ Empty 2 Empty 2 :=
  Rew.subst ![
    (#1 : ArithmeticSemiterm Empty 2),
    (#0 : ArithmeticSemiterm Empty 2)]

def equalityLeftSpecialized (q : ℕ) : ArithmeticSemisentence 2 :=
  canonicalPartrecGraphFormula.val/[
    (↑q : ArithmeticSemiterm Empty 2),
    (#0 : ArithmeticSemiterm Empty 2),
    (#1 : ArithmeticSemiterm Empty 2)]

def equalityRightSpecialized (r : ℕ) : ArithmeticSemisentence 3 :=
  (evalnCertificateFormula : ArithmeticSemisentence 4)/[
    (#0 : ArithmeticSemiterm Empty 3),
    (↑r : ArithmeticSemiterm Empty 3),
    (#1 : ArithmeticSemiterm Empty 3),
    (#2 : ArithmeticSemiterm Empty 3)]

def equalityLeftBody (q _r : ℕ) : ArithmeticSemisentence 2 :=
  (Rew.subst ![
    (↑q : ArithmeticSemiterm Empty 2),
    (#1 : ArithmeticSemiterm Empty 2),
    (#0 : ArithmeticSemiterm Empty 2)]) ▹ canonicalPartrecGraphFormula.val

def equalityRightOpen (_q r : ℕ) : ArithmeticSemisentence 3 :=
  (Rew.subst ![
    (#0 : ArithmeticSemiterm Empty 3),
    (↑r : ArithmeticSemiterm Empty 3),
    (#2 : ArithmeticSemiterm Empty 3),
    (#1 : ArithmeticSemiterm Empty 3)]) ▹
      (evalnCertificateFormula : ArithmeticSemisentence 4)

def directEqualitySentence (q r : ℕ) : ArithmeticSentence :=
  ∀¹ ∀¹ LogicalConnective.iff
    (equalityLeftBody q r) (∃¹ equalityRightOpen q r)

end FailureOfComposition.NumericalProofBridge
