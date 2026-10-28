/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import Arith.FixedFormulaNumeralSubstitution
import FailureOfComposition.NumericalSpecialization
import Foundation.FirstOrder.Arithmetic.Bootstrapping.FixedPoint

/-!
# Proof-presentation bridges for numerical specialization

This module connects PA proofs of the actual first-success and eventual-graph
sentences to the tagged formula codes consumed by the numerical
specialization calculus.  The stage carried by a bridge is explicit numerical
evidence; no proof search or stage extractor is hidden in the construction.
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

/-! ## Codes of the arithmetic sentences represented by the graph tags -/

/-- The fixed three-parameter formula whose closed instances are
first-success graph instances. -/
def leftSentenceTemplate : ArithmeticSemisentence 3 :=
  canonicalPartrecGraphFormula.val

/-- The fixed three-parameter formula whose closed instances are eventual
graph instances. -/
def rightSentenceTemplate : ArithmeticSemisentence 3 :=
  ∃¹ ((evalnCertificateFormula : ArithmeticSemisentence 4)/[
    (#0 : ArithmeticSemiterm Empty 4),
    (#1 : ArithmeticSemiterm Empty 4),
    (#2 : ArithmeticSemiterm Empty 4),
    (#3 : ArithmeticSemiterm Empty 4)])

/-- The fixed two-parameter formula used by the internal substitution graph
for uniform graph equality.  External primitive recursiveness is proved
branchwise below, so elaboration never traverses this combined formula. -/
def equalitySentenceTemplate : ArithmeticSemisentence 2 :=
  ∀¹ ∀¹ LogicalConnective.iff
    (canonicalPartrecGraphFormula.val/[
      (#2 : ArithmeticSemiterm Empty 4),
      (#1 : ArithmeticSemiterm Empty 4),
      (#0 : ArithmeticSemiterm Empty 4)])
    (∃¹ ((evalnCertificateFormula : ArithmeticSemisentence 4)/[
      (#0 : ArithmeticSemiterm Empty 5),
      (#4 : ArithmeticSemiterm Empty 5),
      (#2 : ArithmeticSemiterm Empty 5),
      (#1 : ArithmeticSemiterm Empty 5)]))

/-- The actual `Encodable` code of the uniform comparison sentence. -/
def eqSentenceCode (q r : ℕ) : ℕ :=
  Encodable.encode
    (uniformSentence (firstSuccessGraph q) (eventualGraph r))

/-- The actual `Encodable` code of a closed first-success graph instance. -/
def leftSentenceCode (q n m : ℕ) : ℕ :=
  Encodable.encode
    ((firstSuccessGraph q).val/[n, m] : ArithmeticSentence)

/-- The actual `Encodable` code of a closed eventual-graph instance. -/
def rightSentenceCode (r n m : ℕ) : ℕ :=
  Encodable.encode
    ((eventualGraph r).val/[n, m] : ArithmeticSentence)

theorem eqSentenceCode_eq_encode (q r : ℕ) :
    eqSentenceCode q r =
      Encodable.encode
        (uniformSentence (firstSuccessGraph q) (eventualGraph r)) :=
  rfl

theorem leftSentenceCode_eq_encode (q n m : ℕ) :
    leftSentenceCode q n m =
      Encodable.encode
        ((firstSuccessGraph q).val/[n, m] : ArithmeticSentence) :=
  rfl

theorem rightSentenceCode_eq_encode (r n m : ℕ) :
    rightSentenceCode r n m =
      Encodable.encode
        ((eventualGraph r).val/[n, m] : ArithmeticSentence) :=
  rfl

end FailureOfComposition.NumericalProofBridge
