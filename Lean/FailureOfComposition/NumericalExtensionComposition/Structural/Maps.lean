/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalExtensionComposition.Structural.ProofGraph
public import FailureOfComposition.NumericalExtensionProofs.Structural.Maps
public import FailureOfComposition.NumericalProductProofs.Structural.Maps

/-!
# Arithmetic graphs of the composed B1(7) proof maps

This file defines model-internal values and `𝚺₁` graphs for the two basic maps
and the three nontrivial composites.  It also proves preservation of the
common proof graph.  The old product and checker maps are re-established
inside that graph, so arbitrary proofs accepted by the new checker are valid
inputs.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalExtensionComposition

open FiniteExtensionChecker NumericalDomainOrder NumericalExtensionProofs
open NumericalProductProofs

noncomputable section

private theorem eval_select_projection_axiom_iff
    {V : Type*} [ORingStructure V]
    (phi : ArithmeticSemisentence 5)
    (x y u p a b t i : V) :
    Semiformula.Eval
        (Semiterm.val ![x, y, u, p, a, b, t, i] Empty.elim ∘
          ![(#0 : ArithmeticSemiterm Empty 8), #4, #5, #6, #7])
        Empty.elim phi ↔
      Semiformula.Evalb (M := V) ![x, a, b, t, i] phi := by
  apply Iff.of_eq
  congr 2
  funext j
  fin_cases j <;> rfl

private theorem eval_select_equality_map_iff
    {V : Type*} [ORingStructure V]
    (phi : ArithmeticSemisentence 7)
    (d j y u p q r t i : V) :
    Semiformula.Eval
        (Semiterm.val ![d, j, y, u, p, q, r, t, i] Empty.elim ∘
          ![(#0 : ArithmeticSemiterm Empty 9), #3, #4, #1, #6, #7, #8])
        Empty.elim phi ↔
      Semiformula.Evalb (M := V) ![d, u, p, j, r, t, i] phi := by
  apply Iff.of_eq
  congr 2
  funext k
  fin_cases k <;> rfl

private theorem eval_select_project1_map_iff
    {V : Type*} [ORingStructure V]
    (phi : ArithmeticSemisentence 5)
    (d j y u p q r t i : V) :
    Semiformula.Eval
        (Semiterm.val ![d, j, y, u, p, q, r, t, i] Empty.elim ∘
          ![(#2 : ArithmeticSemiterm Empty 9), #0, #5, #6, #7])
        Empty.elim phi ↔
      Semiformula.Evalb (M := V) ![y, d, q, r, t] phi := by
  apply Iff.of_eq
  congr 2
  funext k
  fin_cases k <;> rfl

private theorem eval_select_projection_pair_map_iff
    {V : Type*} [ORingStructure V]
    (phi : ArithmeticSemisentence 7)
    (d y u p q r t i : V) :
    Semiformula.Eval
        (Semiterm.val ![d, y, u, p, q, r, t, i] Empty.elim ∘
          ![(#0 : ArithmeticSemiterm Empty 8), #2, #3, #4, #5, #6, #7])
        Empty.elim phi ↔
      Semiformula.Evalb (M := V) ![d, u, p, q, r, t, i] phi := by
  apply Iff.of_eq
  congr 2
  funext k
  fin_cases k <;> rfl

private theorem eval_select_pair_to_left_map_iff
    {V : Type*} [ORingStructure V]
    (phi : ArithmeticSemisentence 5)
    (d y u p q r t i : V) :
    Semiformula.Eval
        (Semiterm.val ![d, y, u, p, q, r, t, i] Empty.elim ∘
          ![(#1 : ArithmeticSemiterm Empty 8), #0, #4, #5, #6])
        Empty.elim phi ↔
      Semiformula.Evalb (M := V) ![y, d, q, r, t] phi := by
  apply Iff.of_eq
  congr 2
  funext k
  fin_cases k <;> rfl

private theorem eval_select_component_axiom_iff
    {V : Type*} [ORingStructure V]
    (phi : ArithmeticSemisentence 6)
    (x y v a b q r t c i : V) :
    Semiformula.Eval
        (Semiterm.val ![x, y, v, a, b, q, r, t, c, i] Empty.elim ∘
          ![(#0 : ArithmeticSemiterm Empty 10), #5, #6, #7, #8, #9])
        Empty.elim phi ↔
      Semiformula.Evalb (M := V) ![x, q, r, t, c, i] phi := by
  apply Iff.of_eq
  congr 2
  funext k
  fin_cases k <;> rfl

private theorem eval_select_component_map_iff
    {V : Type*} [ORingStructure V]
    (phi : ArithmeticSemisentence 9)
    (d y v a b q r t c i : V) :
    Semiformula.Eval
        (Semiterm.val ![d, y, v, a, b, q, r, t, c, i] Empty.elim ∘
          ![(#0 : ArithmeticSemiterm Empty 10), #2, #3, #4, #5, #6, #7, #8,
            #9])
        Empty.elim phi ↔
      Semiformula.Evalb (M := V) ![d, v, a, b, q, r, t, c, i] phi := by
  apply Iff.of_eq
  congr 2
  funext k
  fin_cases k <;> rfl

/-! ## Internal values and graphs -/

def equalityValueToDefinednessValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (u p a b t i : V) : V :=
  mpValue
    (mpValue (oneLineProofValue
      (projectionDefinednessAxiomCodeValue a b t i)) u) p

def projectionEqualityToPairValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (u p q r t i : V) : V :=
  project1ToPairValue
    (equalityValueToDefinednessValue u p
      (project1PairIndexValue q r) r t i) q r t

def projectionEqualityToLeftValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (u p q r t i : V) : V :=
  pairToLeftValue (projectionEqualityToPairValue u p q r t i) q r t

def componentValuesToCheckerValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (v a b q r t c i : V) : V :=
  mpValue
    (mpValue
      (mpValue (oneLineProofValue
        (componentValuesToCheckerAxiomCodeValue q r t c i)) v) a) b

def componentValuesToExtValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (v a b q r t c i : V) : V :=
  checkerToExtValue (componentValuesToCheckerValue v a b q r t c i) c i

def equalityValueToDefinednessGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “y u p a b t i.
    ∃ k, !projectionDefinednessAxiomCodeGraph k a b t i ∧
    ∃ s, !oneLineProofGraph s k ∧
    ∃ d, !mpGraph d s u ∧
      !mpGraph y d p”

def projectionEqualityToPairGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “y u p q r t i.
    ∃ j, !project1PairIndexGraph j q r ∧
    ∃ d, !equalityValueToDefinednessGraph d u p j r t i ∧
      !project1ToPairGraph y d q r t”

def projectionEqualityToLeftGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “y u p q r t i.
    ∃ d, !projectionEqualityToPairGraph d u p q r t i ∧
      !pairToLeftGraph y d q r t”

def componentValuesToCheckerGraph : 𝚺₁.Semisentence 9 := .mkSigma
  “y v a b q r t c i.
    ∃ k, !componentValuesToCheckerAxiomCodeGraph k q r t c i ∧
    ∃ s, !oneLineProofGraph s k ∧
    ∃ d, !mpGraph d s v ∧
    ∃ e, !mpGraph e d a ∧
      !mpGraph y e b”

def componentValuesToExtGraph : 𝚺₁.Semisentence 9 := .mkSigma
  “y v a b q r t c i.
    ∃ d, !componentValuesToCheckerGraph d v a b q r t c i ∧
      !checkerToExtGraph y d c i”

theorem equalityValueToDefinednessGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y u p a b t i : V) :
    Semiformula.Evalb (M := V) ![y, u, p, a, b, t, i]
        equalityValueToDefinednessGraph.val ↔
      y = equalityValueToDefinednessValue u p a b t i := by
  simp [equalityValueToDefinednessGraph,
    equalityValueToDefinednessValue, eval_select_projection_axiom_iff,
    projectionDefinednessAxiomCodeGraph_iff,
    oneLineProofGraph_iff, mpGraph_iff_mpValue]

theorem projectionEqualityToPairGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y u p q r t i : V) :
    Semiformula.Evalb (M := V) ![y, u, p, q, r, t, i]
        projectionEqualityToPairGraph.val ↔
      y = projectionEqualityToPairValue u p q r t i := by
  simp [projectionEqualityToPairGraph, projectionEqualityToPairValue,
    eval_select_equality_map_iff, eval_select_project1_map_iff,
    project1PairIndexGraph_iff, equalityValueToDefinednessGraph_iff,
    project1ToPairGraph_iff]

theorem projectionEqualityToLeftGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y u p q r t i : V) :
    Semiformula.Evalb (M := V) ![y, u, p, q, r, t, i]
        projectionEqualityToLeftGraph.val ↔
      y = projectionEqualityToLeftValue u p q r t i := by
  simp [projectionEqualityToLeftGraph, projectionEqualityToLeftValue,
    eval_select_projection_pair_map_iff, eval_select_pair_to_left_map_iff,
    projectionEqualityToPairGraph_iff, pairToLeftGraph_iff]

theorem componentValuesToCheckerGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y v a b q r t c i : V) :
    Semiformula.Evalb (M := V) ![y, v, a, b, q, r, t, c, i]
        componentValuesToCheckerGraph.val ↔
      y = componentValuesToCheckerValue v a b q r t c i := by
  simp [componentValuesToCheckerGraph, componentValuesToCheckerValue,
    eval_select_component_axiom_iff,
    componentValuesToCheckerAxiomCodeGraph_iff,
    oneLineProofGraph_iff, mpGraph_iff_mpValue]

theorem componentValuesToExtGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y v a b q r t c i : V) :
    Semiformula.Evalb (M := V) ![y, v, a, b, q, r, t, c, i]
        componentValuesToExtGraph.val ↔
      y = componentValuesToExtValue v a b q r t c i := by
  simp [componentValuesToExtGraph, componentValuesToExtValue,
    eval_select_component_map_iff,
    componentValuesToCheckerGraph_iff, checkerToExtGraph_iff]

/-! ## Totality and functionality -/

theorem equalityValueToDefinednessGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (u p a b t i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, u, p, a, b, t, i]
      equalityValueToDefinednessGraph.val :=
  ⟨equalityValueToDefinednessValue u p a b t i,
    (equalityValueToDefinednessGraph_iff _ _ _ _ _ _ _).mpr rfl⟩

theorem projectionEqualityToPairGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (u p q r t i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, u, p, q, r, t, i]
      projectionEqualityToPairGraph.val :=
  ⟨projectionEqualityToPairValue u p q r t i,
    (projectionEqualityToPairGraph_iff _ _ _ _ _ _ _).mpr rfl⟩

theorem projectionEqualityToLeftGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (u p q r t i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, u, p, q, r, t, i]
      projectionEqualityToLeftGraph.val :=
  ⟨projectionEqualityToLeftValue u p q r t i,
    (projectionEqualityToLeftGraph_iff _ _ _ _ _ _ _).mpr rfl⟩

theorem componentValuesToCheckerGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (v a b q r t c i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, v, a, b, q, r, t, c, i]
      componentValuesToCheckerGraph.val :=
  ⟨componentValuesToCheckerValue v a b q r t c i,
    (componentValuesToCheckerGraph_iff _ _ _ _ _ _ _ _ _).mpr rfl⟩

theorem componentValuesToExtGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (v a b q r t c i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, v, a, b, q, r, t, c, i]
      componentValuesToExtGraph.val :=
  ⟨componentValuesToExtValue v a b q r t c i,
    (componentValuesToExtGraph_iff _ _ _ _ _ _ _ _ _).mpr rfl⟩

theorem equalityValueToDefinednessGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z u p a b t i : V}
    (hy : Semiformula.Evalb (M := V) ![y, u, p, a, b, t, i]
      equalityValueToDefinednessGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, u, p, a, b, t, i]
      equalityValueToDefinednessGraph.val) : y = z :=
  (equalityValueToDefinednessGraph_iff y u p a b t i).mp hy |>.trans
    ((equalityValueToDefinednessGraph_iff z u p a b t i).mp hz).symm

theorem projectionEqualityToPairGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z u p q r t i : V}
    (hy : Semiformula.Evalb (M := V) ![y, u, p, q, r, t, i]
      projectionEqualityToPairGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, u, p, q, r, t, i]
      projectionEqualityToPairGraph.val) : y = z :=
  (projectionEqualityToPairGraph_iff y u p q r t i).mp hy |>.trans
    ((projectionEqualityToPairGraph_iff z u p q r t i).mp hz).symm

theorem projectionEqualityToLeftGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z u p q r t i : V}
    (hy : Semiformula.Evalb (M := V) ![y, u, p, q, r, t, i]
      projectionEqualityToLeftGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, u, p, q, r, t, i]
      projectionEqualityToLeftGraph.val) : y = z :=
  (projectionEqualityToLeftGraph_iff y u p q r t i).mp hy |>.trans
    ((projectionEqualityToLeftGraph_iff z u p q r t i).mp hz).symm

theorem componentValuesToCheckerGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z v a b q r t c i : V}
    (hy : Semiformula.Evalb (M := V) ![y, v, a, b, q, r, t, c, i]
      componentValuesToCheckerGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, v, a, b, q, r, t, c, i]
      componentValuesToCheckerGraph.val) : y = z :=
  (componentValuesToCheckerGraph_iff y v a b q r t c i).mp hy |>.trans
    ((componentValuesToCheckerGraph_iff z v a b q r t c i).mp hz).symm

theorem componentValuesToExtGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z v a b q r t c i : V}
    (hy : Semiformula.Evalb (M := V) ![y, v, a, b, q, r, t, c, i]
      componentValuesToExtGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, v, a, b, q, r, t, c, i]
      componentValuesToExtGraph.val) : y = z :=
  (componentValuesToExtGraph_iff y v a b q r t c i).mp hy |>.trans
    ((componentValuesToExtGraph_iff z v a b q r t c i).mp hz).symm

/-! ## Standard-natural-number values -/

theorem equalityValueToDefinednessValue_nat
    (u p a b t i : ℕ) :
    equalityValueToDefinednessValue u p a b t i =
      equalityValueToDefinedness u p a b t i := by
  simp [equalityValueToDefinednessValue, equalityValueToDefinedness,
    projectionDefinednessAxiomCodeValue_nat,
    oneLineProofValue_nat, mpValue_nat]

theorem projectionEqualityToPairValue_nat
    (u p q r t i : ℕ) :
    projectionEqualityToPairValue u p q r t i =
      projectionEqualityToPair u p q r t i := by
  simp [projectionEqualityToPairValue, projectionEqualityToPair,
    equalityValueToDefinednessValue_nat, project1PairIndexValue_nat,
    project1ToPairValue_nat]

theorem projectionEqualityToLeftValue_nat
    (u p q r t i : ℕ) :
    projectionEqualityToLeftValue u p q r t i =
      projectionEqualityToLeft u p q r t i := by
  simp [projectionEqualityToLeftValue, projectionEqualityToLeft,
    projectionEqualityToPairValue_nat, pairToLeftValue_nat]

theorem componentValuesToCheckerValue_nat
    (v a b q r t c i : ℕ) :
    componentValuesToCheckerValue v a b q r t c i =
      componentValuesToChecker v a b q r t c i := by
  simp [componentValuesToCheckerValue, componentValuesToChecker,
    componentValuesToCheckerAxiomCodeValue_nat,
    oneLineProofValue_nat, mpValue_nat]

theorem componentValuesToExtValue_nat
    (v a b q r t c i : ℕ) :
    componentValuesToExtValue v a b q r t c i =
      componentValuesToExt v a b q r t c i := by
  simp [componentValuesToExtValue, componentValuesToExt,
    componentValuesToCheckerValue_nat, checkerToExtValue_nat]

/-! ## Internal structural preservation -/

theorem extensionCompositionProofGraph_oneLine
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Th : PRTheoryPresentation) (a : V)
    (ha : Semiformula.Evalb (M := V) ![a]
      extensionCompositionLogicalAxiomLeaf.val) :
    Semiformula.Evalb (M := V) ![oneLineProofValue a, a]
      (proofGraphWithLogicalAxiom Th
        extensionCompositionLogicalAxiomLeaf).val := by
  rw [proofGraphWithLogicalAxiom_iff]
  have hdecode : listDecodeValue (oneLineProofValue a) = a ∷ (0 : V) :=
    listDecodeValue_leftInverse (a ∷ (0 : V))
  rw [hdecode]
  refine ⟨by simp, ?_, ?_⟩
  · simp [lastValue, takeLast_adjoin]
  · intro j hj
    have hj' : j < (1 : V) := by simpa using hj
    have hj0 : j = 0 :=
      le_antisymm (lt_succ_iff_le.mp (by simpa using hj'))
        (Arithmetic.zero_le j)
    subst j
    rw [lineCheckWithLogicalAxiom_iff]
    exact ⟨a, by simp, Or.inl ha⟩

private theorem extensionCompositionLogicalAxiomLeaf_project1ToPair
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r t : V) :
    Semiformula.Evalb (M := V)
      ![project1ToPairAxiomCodeValue q r t]
      extensionCompositionLogicalAxiomLeaf.val := by
  apply extensionCompositionLogicalAxiomLeaf_finiteExtension
  apply finiteExtensionLogicalAxiomLeaf_domainOrder
  apply domainOrderLogicalAxiomLeaf_product
  exact productLogicalAxiomLeaf_project1ToPair q r t

private theorem extensionCompositionLogicalAxiomLeaf_pairToLeft
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r t : V) :
    Semiformula.Evalb (M := V)
      ![pairToLeftAxiomCodeValue q r t]
      extensionCompositionLogicalAxiomLeaf.val := by
  apply extensionCompositionLogicalAxiomLeaf_finiteExtension
  apply finiteExtensionLogicalAxiomLeaf_domainOrder
  apply domainOrderLogicalAxiomLeaf_product
  exact productLogicalAxiomLeaf_pairToLeft q r t

private theorem extensionCompositionLogicalAxiomLeaf_checkerToExtension
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c i : V) :
    Semiformula.Evalb (M := V)
      ![checkerToExtensionAxiomCodeValue c i]
      extensionCompositionLogicalAxiomLeaf.val :=
  extensionCompositionLogicalAxiomLeaf_finiteExtension _
    (finiteExtensionLogicalAxiomLeaf_checkerToExtension c i)

theorem extensionCompositionProofGraph_equalityValueToDefinedness
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (u p a b t i : V)
    (hu : Semiformula.Evalb (M := V)
      ![u, equalityCodeValue a b]
      (extensionCompositionProofGraph w hw).val)
    (hp : Semiformula.Evalb (M := V)
      ![p, rightInstanceCodeValue b t i]
      (extensionCompositionProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![equalityValueToDefinednessValue u p a b t i,
        definednessTagValue a t]
      (extensionCompositionProofGraph w hw).val := by
  let Th := extensionCompositionPRTheoryPresentation w hw
  let e := equalityCodeValue (V := V) a b
  let v := rightInstanceCodeValue (V := V) b t i
  let d := definednessTagValue (V := V) a t
  let l := impValue v d
  let k := projectionDefinednessAxiomCodeValue (V := V) a b t i
  let s := oneLineProofValue k
  let m := mpValue s u
  have hk₁ : Semiformula.Evalb (M := V) ![k, e, l] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hk₂ : Semiformula.Evalb (M := V) ![l, v, d] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hs : Semiformula.Evalb (M := V) ![s, k]
      (proofGraphWithLogicalAxiom Th
        extensionCompositionLogicalAxiomLeaf).val :=
    extensionCompositionProofGraph_oneLine Th k
      (extensionCompositionLogicalAxiomLeaf_projectionDefinedness a b t i)
  have hm₁ : Semiformula.Evalb (M := V) ![m, s, u] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  have hm : Semiformula.Evalb (M := V) ![m, l]
      (extensionCompositionProofGraph w hw).val :=
    proofGraphWithLogicalAxiom_of_mpGraph Th
      extensionCompositionLogicalAxiomLeaf u e k l s m hu hk₁ hs hm₁
  have hm₂ : Semiformula.Evalb (M := V)
      ![equalityValueToDefinednessValue u p a b t i, m, p]
      mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th
    extensionCompositionLogicalAxiomLeaf p v l d m
      (equalityValueToDefinednessValue u p a b t i) hp hk₂ hm hm₂

theorem extensionCompositionProofGraph_project1ToPair
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p q r t : V)
    (hp : Semiformula.Evalb (M := V)
      ![p, definednessTagValue (project1PairIndexValue q r) t]
      (extensionCompositionProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![project1ToPairValue p q r t,
        definednessTagValue (pairIndexValue q r) t]
      (extensionCompositionProofGraph w hw).val := by
  let Th := extensionCompositionPRTheoryPresentation w hw
  let a := definednessTagValue (V := V) (project1PairIndexValue q r) t
  let b := definednessTagValue (V := V) (pairIndexValue q r) t
  let k := project1ToPairAxiomCodeValue (V := V) q r t
  let s := oneLineProofValue k
  have hk : Semiformula.Evalb (M := V) ![k, a, b] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hs : Semiformula.Evalb (M := V) ![s, k]
      (proofGraphWithLogicalAxiom Th
        extensionCompositionLogicalAxiomLeaf).val :=
    extensionCompositionProofGraph_oneLine Th k
      (extensionCompositionLogicalAxiomLeaf_project1ToPair q r t)
  have hm : Semiformula.Evalb (M := V)
      ![project1ToPairValue p q r t, s, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th
    extensionCompositionLogicalAxiomLeaf p a k b s
      (project1ToPairValue p q r t) hp hk hs hm

theorem extensionCompositionProofGraph_pairToLeft
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p q r t : V)
    (hp : Semiformula.Evalb (M := V)
      ![p, definednessTagValue (pairIndexValue q r) t]
      (extensionCompositionProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![pairToLeftValue p q r t, definednessTagValue q t]
      (extensionCompositionProofGraph w hw).val := by
  let Th := extensionCompositionPRTheoryPresentation w hw
  let a := definednessTagValue (V := V) (pairIndexValue q r) t
  let b := definednessTagValue (V := V) q t
  let k := pairToLeftAxiomCodeValue (V := V) q r t
  let s := oneLineProofValue k
  have hk : Semiformula.Evalb (M := V) ![k, a, b] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hs : Semiformula.Evalb (M := V) ![s, k]
      (proofGraphWithLogicalAxiom Th
        extensionCompositionLogicalAxiomLeaf).val :=
    extensionCompositionProofGraph_oneLine Th k
      (extensionCompositionLogicalAxiomLeaf_pairToLeft q r t)
  have hm : Semiformula.Evalb (M := V)
      ![pairToLeftValue p q r t, s, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th
    extensionCompositionLogicalAxiomLeaf p a k b s
      (pairToLeftValue p q r t) hp hk hs hm

theorem extensionCompositionProofGraph_componentValuesToChecker
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (v a b q r t c i : V)
    (hv : Semiformula.Evalb (M := V)
      ![v, equalityCodeValue
        (compIndexValue (ORingStructure.numeral extensionCheckerIndex)
          (pairIndexValue q r)) (pairIndexValue q r)]
      (extensionCompositionProofGraph w hw).val)
    (ha : Semiformula.Evalb (M := V)
      ![a, rightInstanceCodeValue q t c]
      (extensionCompositionProofGraph w hw).val)
    (hb : Semiformula.Evalb (M := V)
      ![b, rightInstanceCodeValue r t i]
      (extensionCompositionProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![componentValuesToCheckerValue v a b q r t c i,
        checkerInstanceCodeValue c i]
      (extensionCompositionProofGraph w hw).val := by
  let Th := extensionCompositionPRTheoryPresentation w hw
  let e := equalityCodeValue (V := V)
    (compIndexValue (ORingStructure.numeral extensionCheckerIndex)
      (pairIndexValue q r)) (pairIndexValue q r)
  let l := rightInstanceCodeValue (V := V) q t c
  let m := rightInstanceCodeValue (V := V) r t i
  let d := checkerInstanceCodeValue (V := V) c i
  let j := impValue m d
  let g := impValue l j
  let k := componentValuesToCheckerAxiomCodeValue (V := V) q r t c i
  let s := oneLineProofValue k
  let x := mpValue s v
  let y := mpValue x a
  have hk₁ : Semiformula.Evalb (M := V) ![k, e, g] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hk₂ : Semiformula.Evalb (M := V) ![g, l, j] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hk₃ : Semiformula.Evalb (M := V) ![j, m, d] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hs : Semiformula.Evalb (M := V) ![s, k]
      (proofGraphWithLogicalAxiom Th
        extensionCompositionLogicalAxiomLeaf).val :=
    extensionCompositionProofGraph_oneLine Th k
      (extensionCompositionLogicalAxiomLeaf_componentValuesToChecker
        q r t c i)
  have hmp₁ : Semiformula.Evalb (M := V) ![x, s, v] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  have hx : Semiformula.Evalb (M := V) ![x, g]
      (extensionCompositionProofGraph w hw).val :=
    proofGraphWithLogicalAxiom_of_mpGraph Th
      extensionCompositionLogicalAxiomLeaf v e k g s x hv hk₁ hs hmp₁
  have hmp₂ : Semiformula.Evalb (M := V) ![y, x, a] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  have hy : Semiformula.Evalb (M := V) ![y, j]
      (extensionCompositionProofGraph w hw).val :=
    proofGraphWithLogicalAxiom_of_mpGraph Th
      extensionCompositionLogicalAxiomLeaf a l g j x y ha hk₂ hx hmp₂
  have hmp₃ : Semiformula.Evalb (M := V)
      ![componentValuesToCheckerValue v a b q r t c i, y, b]
      mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th
    extensionCompositionLogicalAxiomLeaf b m j d y
      (componentValuesToCheckerValue v a b q r t c i)
      hb hk₃ hy hmp₃

theorem extensionCompositionProofGraph_checkerToExt
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p c i : V)
    (hp : Semiformula.Evalb (M := V)
      ![p, checkerInstanceCodeValue c i]
      (extensionCompositionProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![checkerToExtValue p c i, extensionInstanceCodeValue c i]
      (extensionCompositionProofGraph w hw).val := by
  let Th := extensionCompositionPRTheoryPresentation w hw
  let a := checkerInstanceCodeValue (V := V) c i
  let b := extensionInstanceCodeValue (V := V) c i
  let k := checkerToExtensionAxiomCodeValue (V := V) c i
  let s := oneLineProofValue k
  have hk : Semiformula.Evalb (M := V) ![k, a, b] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hs : Semiformula.Evalb (M := V) ![s, k]
      (proofGraphWithLogicalAxiom Th
        extensionCompositionLogicalAxiomLeaf).val :=
    extensionCompositionProofGraph_oneLine Th k
      (extensionCompositionLogicalAxiomLeaf_checkerToExtension c i)
  have hm : Semiformula.Evalb (M := V)
      ![checkerToExtValue p c i, s, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th
    extensionCompositionLogicalAxiomLeaf p a k b s
      (checkerToExtValue p c i) hp hk hs hm

theorem extensionCompositionProofGraph_projectionEqualityToPair
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (u p q r t i : V)
    (hu : Semiformula.Evalb (M := V)
      ![u, equalityCodeValue (project1PairIndexValue q r) r]
      (extensionCompositionProofGraph w hw).val)
    (hp : Semiformula.Evalb (M := V)
      ![p, rightInstanceCodeValue r t i]
      (extensionCompositionProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![projectionEqualityToPairValue u p q r t i,
        definednessTagValue (pairIndexValue q r) t]
      (extensionCompositionProofGraph w hw).val :=
  extensionCompositionProofGraph_project1ToPair w hw _ q r t
    (extensionCompositionProofGraph_equalityValueToDefinedness
      w hw u p (project1PairIndexValue q r) r t i hu hp)

theorem extensionCompositionProofGraph_projectionEqualityToLeft
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (u p q r t i : V)
    (hu : Semiformula.Evalb (M := V)
      ![u, equalityCodeValue (project1PairIndexValue q r) r]
      (extensionCompositionProofGraph w hw).val)
    (hp : Semiformula.Evalb (M := V)
      ![p, rightInstanceCodeValue r t i]
      (extensionCompositionProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![projectionEqualityToLeftValue u p q r t i,
        definednessTagValue q t]
      (extensionCompositionProofGraph w hw).val :=
  extensionCompositionProofGraph_pairToLeft w hw _ q r t
    (extensionCompositionProofGraph_projectionEqualityToPair
      w hw u p q r t i hu hp)

theorem extensionCompositionProofGraph_componentValuesToExt
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (v a b q r t c i : V)
    (hv : Semiformula.Evalb (M := V)
      ![v, equalityCodeValue
        (compIndexValue (ORingStructure.numeral extensionCheckerIndex)
          (pairIndexValue q r)) (pairIndexValue q r)]
      (extensionCompositionProofGraph w hw).val)
    (ha : Semiformula.Evalb (M := V)
      ![a, rightInstanceCodeValue q t c]
      (extensionCompositionProofGraph w hw).val)
    (hb : Semiformula.Evalb (M := V)
      ![b, rightInstanceCodeValue r t i]
      (extensionCompositionProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![componentValuesToExtValue v a b q r t c i,
        extensionInstanceCodeValue c i]
      (extensionCompositionProofGraph w hw).val :=
  extensionCompositionProofGraph_checkerToExt w hw _ c i
    (extensionCompositionProofGraph_componentValuesToChecker
      w hw v a b q r t c i hv ha hb)

end

end FailureOfComposition.NumericalExtensionComposition
