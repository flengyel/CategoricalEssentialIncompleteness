/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalExtensionComposition.Soundness
public import FailureOfComposition.NumericalExtensionProofs.Structural.Codes

/-!
# Arithmetic graphs of the extension-composition scheme codes

The two code builders are interpreted on arbitrary PA-model elements.  Their
graphs expose every program-index constructor and endpoint-code constructor,
so later preservation theorems do not treat external primitive-recursive
functions as opaque.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalExtensionComposition

open FiniteExtensionChecker NumericalExtensionProofs NumericalProofBridge
open NumericalProductProofs

noncomputable section

def projectionDefinednessAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a b t i : V) : V :=
  impValue (equalityCodeValue a b)
    (impValue (rightInstanceCodeValue b t i)
      (definednessTagValue a t))

def componentValuesToCheckerAxiomCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r t c i : V) : V :=
  let p := pairIndexValue q r
  let s := compIndexValue
    (ORingStructure.numeral extensionCheckerIndex : V) p
  impValue (equalityCodeValue s p)
    (impValue (rightInstanceCodeValue q t c)
      (impValue (rightInstanceCodeValue r t i)
        (checkerInstanceCodeValue c i)))

def projectionDefinednessAxiomCodeGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “y a b t i.
    ∃ e, !equalityCodeGraph e a b ∧
    ∃ v, !rightInstanceCodeGraph v b t i ∧
    ∃ d, !definednessTagGraph d a t ∧
    ∃ u, !impGraph u v d ∧
      !impGraph y e u”

def componentValuesToCheckerAxiomCodeGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “y q r t c i.
    ∃ p, !pairIndexGraph p q r ∧
    ∃ s, !compIndexGraph s !!(extensionCheckerIndex) p ∧
    ∃ e, !equalityCodeGraph e s p ∧
    ∃ a, !rightInstanceCodeGraph a q t c ∧
    ∃ b, !rightInstanceCodeGraph b r t i ∧
    ∃ d, !checkerInstanceCodeGraph d c i ∧
    ∃ u, !impGraph u b d ∧
    ∃ v, !impGraph v a u ∧
      !impGraph y e v”

/-- The first scheme-code graph with its output in the last coordinate.  This
ordering lets the proof-graph leaf existentially close the four parameters
without substituting a large graph formula. -/
def projectionDefinednessAxiomCodeGraphOutputLast :
    𝚺₁.Semisentence 5 := .mkSigma
  “a b t i y.
    ∃ e, !equalityCodeGraph e a b ∧
    ∃ v, !rightInstanceCodeGraph v b t i ∧
    ∃ d, !definednessTagGraph d a t ∧
    ∃ u, !impGraph u v d ∧
      !impGraph y e u”

/-- The second scheme-code graph with its output in the last coordinate. -/
def componentValuesToCheckerAxiomCodeGraphOutputLast :
    𝚺₁.Semisentence 6 := .mkSigma
  “q r t c i y.
    ∃ p, !pairIndexGraph p q r ∧
    ∃ s, !compIndexGraph s !!(extensionCheckerIndex) p ∧
    ∃ e, !equalityCodeGraph e s p ∧
    ∃ a, !rightInstanceCodeGraph a q t c ∧
    ∃ b, !rightInstanceCodeGraph b r t i ∧
    ∃ d, !checkerInstanceCodeGraph d c i ∧
    ∃ u, !impGraph u b d ∧
    ∃ v, !impGraph v a u ∧
      !impGraph y e v”

theorem projectionDefinednessAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y a b t i : V) :
    Semiformula.Evalb (M := V) ![y, a, b, t, i]
        projectionDefinednessAxiomCodeGraph.val ↔
      y = projectionDefinednessAxiomCodeValue a b t i := by
  simp [projectionDefinednessAxiomCodeGraph,
    projectionDefinednessAxiomCodeValue, equalityCodeGraph_iff,
    rightInstanceCodeGraph_iff, definednessTagGraph_iff,
    impGraph_iff_impValue]

theorem componentValuesToCheckerAxiomCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q r t c i : V) :
    Semiformula.Evalb (M := V) ![y, q, r, t, c, i]
        componentValuesToCheckerAxiomCodeGraph.val ↔
      y = componentValuesToCheckerAxiomCodeValue q r t c i := by
  simp [componentValuesToCheckerAxiomCodeGraph,
    componentValuesToCheckerAxiomCodeValue, pairIndexGraph_iff,
    compIndexGraph_iff, equalityCodeGraph_iff,
    rightInstanceCodeGraph_iff, checkerInstanceCodeGraph_iff,
    impGraph_iff_impValue, Tarski.Structure.numeral_eq_numeral]

theorem projectionDefinednessAxiomCodeGraphOutputLast_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (a b t i y : V) :
    Semiformula.Evalb (M := V) ![a, b, t, i, y]
        projectionDefinednessAxiomCodeGraphOutputLast.val ↔
      y = projectionDefinednessAxiomCodeValue a b t i := by
  simp [projectionDefinednessAxiomCodeGraphOutputLast,
    projectionDefinednessAxiomCodeValue, equalityCodeGraph_iff,
    rightInstanceCodeGraph_iff, definednessTagGraph_iff,
    impGraph_iff_impValue]

theorem componentValuesToCheckerAxiomCodeGraphOutputLast_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r t c i y : V) :
    Semiformula.Evalb (M := V) ![q, r, t, c, i, y]
        componentValuesToCheckerAxiomCodeGraphOutputLast.val ↔
      y = componentValuesToCheckerAxiomCodeValue q r t c i := by
  simp [componentValuesToCheckerAxiomCodeGraphOutputLast,
    componentValuesToCheckerAxiomCodeValue, pairIndexGraph_iff,
    compIndexGraph_iff, equalityCodeGraph_iff,
    rightInstanceCodeGraph_iff, checkerInstanceCodeGraph_iff,
    impGraph_iff_impValue, Tarski.Structure.numeral_eq_numeral]

theorem projectionDefinednessAxiomCodeGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (a b t i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, a, b, t, i]
      projectionDefinednessAxiomCodeGraph.val :=
  ⟨projectionDefinednessAxiomCodeValue a b t i,
    (projectionDefinednessAxiomCodeGraph_iff _ _ _ _ _).mpr rfl⟩

theorem componentValuesToCheckerAxiomCodeGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r t c i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, q, r, t, c, i]
      componentValuesToCheckerAxiomCodeGraph.val :=
  ⟨componentValuesToCheckerAxiomCodeValue q r t c i,
    (componentValuesToCheckerAxiomCodeGraph_iff _ _ _ _ _ _).mpr rfl⟩

theorem projectionDefinednessAxiomCodeGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z a b t i : V}
    (hy : Semiformula.Evalb (M := V) ![y, a, b, t, i]
      projectionDefinednessAxiomCodeGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, a, b, t, i]
      projectionDefinednessAxiomCodeGraph.val) :
    y = z :=
  (projectionDefinednessAxiomCodeGraph_iff y a b t i).mp hy |>.trans
    ((projectionDefinednessAxiomCodeGraph_iff z a b t i).mp hz).symm

theorem componentValuesToCheckerAxiomCodeGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z q r t c i : V}
    (hy : Semiformula.Evalb (M := V) ![y, q, r, t, c, i]
      componentValuesToCheckerAxiomCodeGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, q, r, t, c, i]
      componentValuesToCheckerAxiomCodeGraph.val) :
    y = z :=
  (componentValuesToCheckerAxiomCodeGraph_iff y q r t c i).mp hy |>.trans
    ((componentValuesToCheckerAxiomCodeGraph_iff z q r t c i).mp hz).symm

theorem projectionDefinednessAxiomCodeValue_nat
    (a b t i : ℕ) :
    projectionDefinednessAxiomCodeValue a b t i =
      projectionDefinednessAxiomCode a b t i := by
  simp [projectionDefinednessAxiomCodeValue, equalityCodeValue_nat,
    rightInstanceCodeValue_nat, definednessTagValue_nat, impValue_nat,
    projectionDefinednessAxiomCode_eq_imp]

theorem componentValuesToCheckerAxiomCodeValue_nat
    (q r t c i : ℕ) :
    componentValuesToCheckerAxiomCodeValue q r t c i =
      componentValuesToCheckerAxiomCode q r t c i := by
  simp [componentValuesToCheckerAxiomCodeValue, pairIndexValue_nat,
    compIndexValue_nat, equalityCodeValue_nat, rightInstanceCodeValue_nat,
    checkerInstanceCodeValue_nat, impValue_nat,
    componentValuesToCheckerAxiomCode_eq_imp, numeral_eq_natCast_app]

end

end FailureOfComposition.NumericalExtensionComposition
