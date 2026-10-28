/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalProofBridge.Core.Codes.Substitution

/-!
# Primitive-recursive proof-presentation sentence codes

This layer proves primitive recursiveness of the three actual sentence-code builders.
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

theorem primrec₂_eqSentenceCode : Primrec₂ eqSentenceCode := by
  have hleft : Primrec (fun z : ℕ × ℕ =>
      equalityLeftBody z.1 z.2) :=
    primrec₂_firstNumeralUnderTwoBinders canonicalPartrecGraphFormula.val
  have hrightOpen : Primrec (fun z : ℕ × ℕ =>
      equalityRightOpen z.1 z.2) :=
    primrec₂_secondNumeralUnderStageAndTwoBinders
      (evalnCertificateFormula : ArithmeticSemisentence 4)
  have hright : Primrec (fun z : ℕ × ℕ =>
      (∃¹ equalityRightOpen z.1 z.2 : ArithmeticSemisentence 2)) :=
    primrec_formulaExs hrightOpen
  have hiff : Primrec (fun z : ℕ × ℕ =>
      LogicalConnective.iff
        (equalityLeftBody z.1 z.2) (∃¹ equalityRightOpen z.1 z.2)) :=
    primrec_formulaIff.comp hleft hright
  have hall₁ : Primrec (fun z : ℕ × ℕ =>
      (∀¹ LogicalConnective.iff
        (equalityLeftBody z.1 z.2) (∃¹ equalityRightOpen z.1 z.2) :
          ArithmeticSemisentence 1)) :=
    primrec_formulaAll hiff
  have hall₂ : Primrec (fun z : ℕ × ℕ =>
      directEqualitySentence z.1 z.2) :=
    primrec_formulaAll hall₁
  refine (Primrec.encode.comp hall₂).of_eq ?_
  intro z
  simp only [eqSentenceCode]
  rw [directEqualitySentence_eq]

theorem primrec_leftSentenceCode :
    Primrec (fun z : (ℕ × ℕ) × ℕ =>
      leftSentenceCode z.1.1 z.1.2 z.2) := by
  refine (Primrec.encode.comp
    (primrec_arithmeticSemisentenceNumeralSubst₃ leftSentenceTemplate)).of_eq ?_
  intro z
  simp only [leftSentenceCode]
  rw [leftSentenceTemplate_subst]

theorem primrec_rightSentenceCode :
    Primrec (fun z : (ℕ × ℕ) × ℕ =>
      rightSentenceCode z.1.1 z.1.2 z.2) := by
  refine (Primrec.encode.comp
    (primrec_arithmeticSemisentenceNumeralSubst₃ rightSentenceTemplate)).of_eq ?_
  intro z
  simp only [rightSentenceCode]
  rw [rightSentenceTemplate_subst]

end FailureOfComposition.NumericalProofBridge
