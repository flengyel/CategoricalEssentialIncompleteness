/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProofBridge.Core

/-!
# Arithmetic graphs of the proof bridge sentence codes
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

def equalitySentenceTemplateCode : ℕ :=
  Encodable.encode equalitySentenceTemplate

def leftSentenceTemplateCode : ℕ :=
  Encodable.encode leftSentenceTemplate

def rightSentenceTemplateCode : ℕ :=
  Encodable.encode rightSentenceTemplate

noncomputable def substTwoSentenceCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c : ℕ) (q r : V) : V :=
  Bootstrapping.Arithmetic.substNumerals
    (ORingStructure.numeral c : V) ![q, r]

noncomputable def substThreeSentenceCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c : ℕ) (q n m : V) : V :=
  Bootstrapping.Arithmetic.substNumerals
    (ORingStructure.numeral c : V) ![q, n, m]

noncomputable def eqSentenceCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r : V) : V :=
  substTwoSentenceCodeValue equalitySentenceTemplateCode q r

noncomputable def leftSentenceCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q n m : V) : V :=
  substThreeSentenceCodeValue leftSentenceTemplateCode q n m

noncomputable def rightSentenceCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (r n m : V) : V :=
  substThreeSentenceCodeValue rightSentenceTemplateCode r n m

noncomputable def substTwoSentenceCodeGraph (c : ℕ) :
    𝚺₁.Semisentence 3 :=
  (Bootstrapping.Arithmetic.ssnums (k := 2)).rew
    (Rew.subst ![
      (#0 : ArithmeticSemiterm Empty 3),
      (↑c : ArithmeticSemiterm Empty 3),
      #1, #2])

noncomputable def substThreeSentenceCodeGraph (c : ℕ) :
    𝚺₁.Semisentence 4 :=
  (Bootstrapping.Arithmetic.ssnums (k := 3)).rew
    (Rew.subst ![
      (#0 : ArithmeticSemiterm Empty 4),
      (↑c : ArithmeticSemiterm Empty 4),
      #1, #2, #3])

noncomputable def eqSentenceCodeGraph : 𝚺₁.Semisentence 3 :=
  substTwoSentenceCodeGraph equalitySentenceTemplateCode

noncomputable def leftSentenceCodeGraph : 𝚺₁.Semisentence 4 :=
  substThreeSentenceCodeGraph leftSentenceTemplateCode

noncomputable def rightSentenceCodeGraph : 𝚺₁.Semisentence 4 :=
  substThreeSentenceCodeGraph rightSentenceTemplateCode

theorem substTwoSentenceCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c : ℕ) (y q r : V) :
    Semiformula.Evalb (M := V) ![y, q, r]
        (substTwoSentenceCodeGraph c).val ↔
      y = substTwoSentenceCodeValue c q r := by
  simp [substTwoSentenceCodeGraph, substTwoSentenceCodeValue,
    Function.comp_def, Matrix.empty_eq, Matrix.fun_eq_vec_two,
    Tarski.Structure.numeral_eq_numeral]

theorem substThreeSentenceCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c : ℕ) (y q n m : V) :
    Semiformula.Evalb (M := V) ![y, q, n, m]
        (substThreeSentenceCodeGraph c).val ↔
      y = substThreeSentenceCodeValue c q n m := by
  simp [substThreeSentenceCodeGraph, substThreeSentenceCodeValue,
    Function.comp_def, Matrix.empty_eq, Matrix.fun_eq_vec_three,
    Tarski.Structure.numeral_eq_numeral]

theorem eqSentenceCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y q r : V) :
    Semiformula.Evalb (M := V) ![y, q, r] eqSentenceCodeGraph.val ↔
      y = eqSentenceCodeValue q r := by
  simpa only [eqSentenceCodeGraph, eqSentenceCodeValue] using
    (substTwoSentenceCodeGraph_iff equalitySentenceTemplateCode y q r)

theorem leftSentenceCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y q n m : V) :
    Semiformula.Evalb (M := V) ![y, q, n, m]
        leftSentenceCodeGraph.val ↔
      y = leftSentenceCodeValue q n m := by
  simpa only [leftSentenceCodeGraph, leftSentenceCodeValue] using
    (substThreeSentenceCodeGraph_iff leftSentenceTemplateCode y q n m)

theorem rightSentenceCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y r n m : V) :
    Semiformula.Evalb (M := V) ![y, r, n, m]
        rightSentenceCodeGraph.val ↔
      y = rightSentenceCodeValue r n m := by
  simpa only [rightSentenceCodeGraph, rightSentenceCodeValue] using
    (substThreeSentenceCodeGraph_iff rightSentenceTemplateCode y r n m)

theorem substTwoSentenceCodeValue_encode
    (phi : ArithmeticSemisentence 2) (q r : ℕ) :
    substTwoSentenceCodeValue (Encodable.encode phi) q r =
      Encodable.encode (phi/[
        (q : ArithmeticSemiterm Empty 0),
        (r : ArithmeticSemiterm Empty 0)]) := by
  rw [substTwoSentenceCodeValue, numeral_eq_natCast_app]
  rw [← Sentence.quote_eq_encode_nat phi,
    ← Sentence.quote_eq_encode_nat (phi/[
      (q : ArithmeticSemiterm Empty 0),
      (r : ArithmeticSemiterm Empty 0)])]
  convert (Bootstrapping.Arithmetic.substNumerals_app_quote
    (V := ℕ) phi ![q, r]) using 1 <;>
    simp [Matrix.fun_eq_vec_two]

theorem substThreeSentenceCodeValue_encode
    (phi : ArithmeticSemisentence 3) (q n m : ℕ) :
    substThreeSentenceCodeValue (Encodable.encode phi) q n m =
      Encodable.encode (phi/[
        (q : ArithmeticSemiterm Empty 0),
        (n : ArithmeticSemiterm Empty 0),
        (m : ArithmeticSemiterm Empty 0)]) := by
  rw [substThreeSentenceCodeValue, numeral_eq_natCast_app]
  rw [← Sentence.quote_eq_encode_nat phi,
    ← Sentence.quote_eq_encode_nat (phi/[
      (q : ArithmeticSemiterm Empty 0),
      (n : ArithmeticSemiterm Empty 0),
      (m : ArithmeticSemiterm Empty 0)])]
  convert (Bootstrapping.Arithmetic.substNumerals_app_quote
    (V := ℕ) phi ![q, n, m]) using 1 <;>
    simp [Matrix.fun_eq_vec_three]

theorem eqSentenceCodeValue_nat (q r : ℕ) :
    eqSentenceCodeValue q r = eqSentenceCode q r := by
  unfold eqSentenceCodeValue equalitySentenceTemplateCode eqSentenceCode
  rw [substTwoSentenceCodeValue_encode, equalitySentenceTemplate_subst]

theorem leftSentenceCodeValue_nat (q n m : ℕ) :
    leftSentenceCodeValue q n m = leftSentenceCode q n m := by
  unfold leftSentenceCodeValue leftSentenceTemplateCode leftSentenceCode
  rw [substThreeSentenceCodeValue_encode, leftSentenceTemplate_subst]

theorem rightSentenceCodeValue_nat (r n m : ℕ) :
    rightSentenceCodeValue r n m = rightSentenceCode r n m := by
  unfold rightSentenceCodeValue rightSentenceTemplateCode rightSentenceCode
  rw [substThreeSentenceCodeValue_encode, rightSentenceTemplate_subst]

end FailureOfComposition.NumericalProofBridge
