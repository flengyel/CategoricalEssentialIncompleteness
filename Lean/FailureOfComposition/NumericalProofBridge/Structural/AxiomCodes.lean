/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProofBridge.Structural.Codes

/-!
# Arithmetic graphs of the numerical proof bridge axioms
-/

@[expose] public section

set_option autoImplicit false
open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural
open Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.NumericalProofBridge

open ProofSearch ConcreteEvaluator

noncomputable def bridgeEqualityAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r s : V) : V :=
  impValue
    (stageCodeValue (eqSentenceCodeValue q r) s)
    (equalityCodeValue q r)

noncomputable def bridgeLeftAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q n m s : V) : V :=
  impValue
    (stageCodeValue (leftSentenceCodeValue q n m) s)
    (leftInstanceCodeValue q n m)

noncomputable def bridgeRightAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (r n m s : V) : V :=
  impValue
    (stageCodeValue (rightSentenceCodeValue r n m) s)
    (rightInstanceCodeValue r n m)

noncomputable def bridgeEqualityAxiomCodeGraph :
    𝚺₁.Semisentence 4 := .mkSigma
  “y q r s.
    ∃ a, !eqSentenceCodeGraph a q r ∧
    ∃ u, !stageCodeGraph u a s ∧
    ∃ e, !equalityCodeGraph e q r ∧
      !impGraph y u e”

noncomputable def bridgeLeftAxiomCodeGraph :
    𝚺₁.Semisentence 5 := .mkSigma
  “y q n m s.
    ∃ a, !leftSentenceCodeGraph a q n m ∧
    ∃ u, !stageCodeGraph u a s ∧
    ∃ f, !leftInstanceCodeGraph f q n m ∧
      !impGraph y u f”

noncomputable def bridgeRightAxiomCodeGraph :
    𝚺₁.Semisentence 5 := .mkSigma
  “y r n m s.
    ∃ a, !rightSentenceCodeGraph a r n m ∧
    ∃ u, !stageCodeGraph u a s ∧
    ∃ g, !rightInstanceCodeGraph g r n m ∧
      !impGraph y u g”

theorem bridgeEqualityAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y q r s : V) :
    Semiformula.Evalb (M := V) ![y, q, r, s]
        bridgeEqualityAxiomCodeGraph.val ↔
      y = bridgeEqualityAxiomCodeValue q r s := by
  simp [bridgeEqualityAxiomCodeGraph, bridgeEqualityAxiomCodeValue,
    eqSentenceCodeGraph_iff, stageCodeGraph_iff, equalityCodeGraph_iff,
    impGraph_iff_impValue]

theorem bridgeLeftAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y q n m s : V) :
    Semiformula.Evalb (M := V) ![y, q, n, m, s]
        bridgeLeftAxiomCodeGraph.val ↔
      y = bridgeLeftAxiomCodeValue q n m s := by
  simp [bridgeLeftAxiomCodeGraph, bridgeLeftAxiomCodeValue,
    leftSentenceCodeGraph_iff, stageCodeGraph_iff,
    leftInstanceCodeGraph_iff, impGraph_iff_impValue]

theorem bridgeRightAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (y r n m s : V) :
    Semiformula.Evalb (M := V) ![y, r, n, m, s]
        bridgeRightAxiomCodeGraph.val ↔
      y = bridgeRightAxiomCodeValue r n m s := by
  simp [bridgeRightAxiomCodeGraph, bridgeRightAxiomCodeValue,
    rightSentenceCodeGraph_iff, stageCodeGraph_iff,
    rightInstanceCodeGraph_iff, impGraph_iff_impValue]

theorem bridgeEqualityAxiomCodeValue_nat (q r s : ℕ) :
    bridgeEqualityAxiomCodeValue q r s =
      bridgeEqualityAxiomCode q r s := by
  rw [bridgeEqualityAxiomCodeValue, impValue_nat, stageCodeValue_nat,
    eqSentenceCodeValue_nat, equalityCodeValue_nat,
    bridgeEqualityAxiomCode_eq_imp]

theorem bridgeLeftAxiomCodeValue_nat (q n m s : ℕ) :
    bridgeLeftAxiomCodeValue q n m s =
      bridgeLeftAxiomCode q n m s := by
  rw [bridgeLeftAxiomCodeValue, impValue_nat, stageCodeValue_nat,
    leftSentenceCodeValue_nat, leftInstanceCodeValue_nat,
    bridgeLeftAxiomCode_eq_imp]

theorem bridgeRightAxiomCodeValue_nat (r n m s : ℕ) :
    bridgeRightAxiomCodeValue r n m s =
      bridgeRightAxiomCode r n m s := by
  rw [bridgeRightAxiomCodeValue, impValue_nat, stageCodeValue_nat,
    rightSentenceCodeValue_nat, rightInstanceCodeValue_nat,
    bridgeRightAxiomCode_eq_imp]

end FailureOfComposition.NumericalProofBridge
