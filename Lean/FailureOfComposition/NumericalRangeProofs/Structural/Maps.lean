/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalRangeProofs.Structural.ProofGraph
public import FailureOfComposition.NumericalProofBridge.Structural.BridgeMaps

/-!
# Arithmetic graph of the range proof map

The external primitive-recursive transformation is represented by a total,
functional Sigma-one graph.  The structural preservation lemmas below build
the computation line, apply the ordinary right-instance bridge, and finally
apply the fixed range-introduction line inside arbitrary PA models.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.NumericalRangeProofs

open NumericalProofBridge

private theorem eval_select_computation_code_iff
    {V : Type*} [ORingStructure V]
    (c p e s u i : V) :
    Semiformula.Eval
        (Semiterm.val ![c, p, e, s, u, i] Empty.elim ∘
          ![(#0 : ArithmeticSemiterm Empty 6), #2, #3, #4, #5])
        Empty.elim computationAxiomCodeGraph.val ↔
      Semiformula.Evalb (M := V) ![c, e, s, u, i]
        computationAxiomCodeGraph.val := by
  apply Iff.of_eq
  congr 2
  funext j
  fin_cases j <;> rfl

private theorem eval_select_computation_stage_iff
    {V : Type*} [ORingStructure V]
    (k h c p e s u i : V) :
    Semiformula.Eval
        (Semiterm.val ![k, h, c, p, e, s, u, i] Empty.elim ∘
          ![(#0 : ArithmeticSemiterm Empty 8), #4, #5, #6, #7])
        Empty.elim computationStageGraph.val ↔
      Semiformula.Evalb (M := V) ![k, e, s, u, i]
        computationStageGraph.val := by
  apply Iff.of_eq
  congr 2
  funext j
  fin_cases j <;> rfl

private theorem eval_select_bridge_right_iff
    {V : Type*} [ORingStructure V]
    (k h c p e s u i : V) :
    Semiformula.Eval
        (Semiterm.val ![k, h, c, p, e, s, u, i] Empty.elim ∘
          ![(#3 : ArithmeticSemiterm Empty 8), #1, #0, #4, #6, #7])
        Empty.elim bridgeRightGraph.val ↔
      Semiformula.Evalb (M := V) ![p, h, k, e, u, i]
        bridgeRightGraph.val := by
  apply Iff.of_eq
  congr 2
  funext j
  fin_cases j <;> rfl

private theorem eval_select_range_code_iff
    {V : Type*} [ORingStructure V]
    (c p e r s u i : V) :
    Semiformula.Eval
        (Semiterm.val ![c, p, e, r, s, u, i] Empty.elim ∘
          ![(#0 : ArithmeticSemiterm Empty 7), #2, #3, #5, #6])
        Empty.elim rangeIntroAxiomCodeGraph.val ↔
      Semiformula.Evalb (M := V) ![c, e, r, u, i]
        rangeIntroAxiomCodeGraph.val := by
  apply Iff.of_eq
  congr 2
  funext j
  fin_cases j <;> rfl

/-! ## Values and graphs -/

noncomputable def computationToRightProofValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e s u i : V) : V :=
  bridgeRightValue
    (oneLineProofValue (computationAxiomCodeValue e s u i))
    (computationStageValue e s u i) e u i

noncomputable def computationToRightProofGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “p e s u i.
    ∃ c, !computationAxiomCodeGraph c e s u i ∧
    ∃ h, !oneLineProofGraph h c ∧
    ∃ k, !computationStageGraph k e s u i ∧
      !bridgeRightGraph p h k e u i”

theorem computationToRightProofGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p e s u i : V) :
    Semiformula.Evalb (M := V) ![p, e, s, u, i]
        computationToRightProofGraph.val ↔
      p = computationToRightProofValue e s u i := by
  simp [computationToRightProofGraph, computationToRightProofValue,
    eval_select_computation_code_iff,
    eval_select_computation_stage_iff, eval_select_bridge_right_iff,
    computationAxiomCodeGraph_iff, oneLineProofGraph_iff,
    computationStageGraph_iff, bridgeRightGraph_iff]

private theorem eval_select_computation_proof_iff
    {V : Type*} [ORingStructure V]
    (q h c p e r s u i : V) :
    Semiformula.Eval
        (Semiterm.val ![q, h, c, p, e, r, s, u, i] Empty.elim ∘
          ![(#0 : ArithmeticSemiterm Empty 9), #4, #6, #7, #8])
        Empty.elim computationToRightProofGraph.val ↔
      Semiformula.Evalb (M := V) ![q, e, s, u, i]
        computationToRightProofGraph.val := by
  apply Iff.of_eq
  congr 2
  funext j
  fin_cases j <;> rfl

noncomputable def rangeProofValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e r s u i : V) : V :=
  mpValue (oneLineProofValue (rangeIntroAxiomCodeValue e r u i))
    (computationToRightProofValue e s u i)

noncomputable def rangeProofMapGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “p e r s u i.
    ∃ c, !rangeIntroAxiomCodeGraph c e r u i ∧
    ∃ h, !oneLineProofGraph h c ∧
    ∃ q, !computationToRightProofGraph q e s u i ∧
      !mpGraph p h q”

theorem rangeProofMapGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p e r s u i : V) :
    Semiformula.Evalb (M := V) ![p, e, r, s, u, i]
        rangeProofMapGraph.val ↔
      p = rangeProofValue e r s u i := by
  simp [rangeProofMapGraph, rangeProofValue,
    eval_select_range_code_iff, eval_select_computation_proof_iff,
    rangeIntroAxiomCodeGraph_iff, oneLineProofGraph_iff,
    computationToRightProofGraph_iff, mpGraph_iff_mpValue]

theorem rangeProofMapGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e r s u i : V) :
    ∃ p : V, Semiformula.Evalb (M := V) ![p, e, r, s, u, i]
      rangeProofMapGraph.val :=
  ⟨rangeProofValue e r s u i,
    (rangeProofMapGraph_iff _ _ _ _ _ _).mpr rfl⟩

theorem rangeProofMapGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {p q e r s u i : V}
    (hp : Semiformula.Evalb (M := V) ![p, e, r, s, u, i]
      rangeProofMapGraph.val)
    (hq : Semiformula.Evalb (M := V) ![q, e, r, s, u, i]
      rangeProofMapGraph.val) : p = q :=
  (rangeProofMapGraph_iff p e r s u i).mp hp |>.trans
    ((rangeProofMapGraph_iff q e r s u i).mp hq).symm

theorem computationToRightProofValue_nat (e s u i : ℕ) :
    computationToRightProofValue e s u i =
      computationToRightProof e s u i := by
  simp [computationToRightProofValue, computationToRightProof,
    computationAxiomCodeValue_nat, computationStageValue_nat,
    oneLineProofValue_nat, bridgeRightValue_nat]

theorem rangeProofValue_nat (e r s u i : ℕ) :
    rangeProofValue e r s u i = rangeProof e r s u i := by
  simp [rangeProofValue, rangeProof, rangeIntroAxiomCodeValue_nat,
    computationToRightProofValue_nat, oneLineProofValue_nat, mpValue_nat]

/-! ## Internal structural preservation -/

theorem rangeProofGraph_oneLine
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e r : ℕ) (Th : PRTheoryPresentation) (a : V)
    (ha : Semiformula.Evalb (M := V) ![a]
      (rangeLogicalAxiomLeaf e r).val) :
    Semiformula.Evalb (M := V) ![oneLineProofValue a, a]
      (proofGraphWithLogicalAxiom Th (rangeLogicalAxiomLeaf e r)).val := by
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

theorem rangeProofGraph_computationToRight
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e r : ℕ) (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (s u i : V)
    (hs : Semiformula.Evalb (M := V)
      ![s, ORingStructure.numeral e, u, i]
      (evalnCertificateFormula : ArithmeticSemisentence 4)) :
    Semiformula.Evalb (M := V)
      ![computationToRightProofValue
          (ORingStructure.numeral e) s u i,
        rightInstanceCodeValue (ORingStructure.numeral e) u i]
      (rangeProofGraph e r w hw).val := by
  let Th := rangePRTheoryPresentation e r w hw
  let en : V := ORingStructure.numeral e
  let c := computationAxiomCodeValue en s u i
  let p := oneLineProofValue c
  let k := computationStageValue en s u i
  let b := bridgeRightAxiomCodeValue en u i k
  let h := oneLineProofValue b
  let a := stageCodeValue (rightSentenceCodeValue en u i) k
  let g := rightInstanceCodeValue en u i
  have hc : c = a := by rfl
  have hp : Semiformula.Evalb (M := V) ![p, a]
      (proofGraphWithLogicalAxiom Th (rangeLogicalAxiomLeaf e r)).val := by
    rw [← hc]
    exact rangeProofGraph_oneLine e r Th c
      (rangeLogicalAxiomLeaf_computation e r en s u i hs)
  have hb : Semiformula.Evalb (M := V) ![b, a, g] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hh : Semiformula.Evalb (M := V) ![h, b]
      (proofGraphWithLogicalAxiom Th (rangeLogicalAxiomLeaf e r)).val :=
    rangeProofGraph_oneLine e r Th b
      (rangeLogicalAxiomLeaf_extended e r b
        (extendedLogicalAxiomLeaf_bridgeRight en u i k))
  have hm : Semiformula.Evalb (M := V)
      ![bridgeRightValue p k en u i, h, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th
    (rangeLogicalAxiomLeaf e r) p a b g h
      (bridgeRightValue p k en u i) hp hb hh hm

theorem rangeProofGraph_rangeProof
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e r : ℕ) (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (s u i : V)
    (hs : Semiformula.Evalb (M := V)
      ![s, ORingStructure.numeral e, u, i]
      (evalnCertificateFormula : ArithmeticSemisentence 4)) :
    Semiformula.Evalb (M := V)
      ![rangeProofValue (ORingStructure.numeral e)
          (ORingStructure.numeral r) s u i,
        rightInstanceCodeValue (ORingStructure.numeral r) i i]
      (rangeProofGraph e r w hw).val := by
  let Th := rangePRTheoryPresentation e r w hw
  let en : V := ORingStructure.numeral e
  let rn : V := ORingStructure.numeral r
  let a := rightInstanceCodeValue en u i
  let d := rightInstanceCodeValue rn i i
  let c := rangeIntroAxiomCodeValue en rn u i
  let h := oneLineProofValue c
  let p := computationToRightProofValue en s u i
  have hp : Semiformula.Evalb (M := V) ![p, a]
      (proofGraphWithLogicalAxiom Th (rangeLogicalAxiomLeaf e r)).val :=
    rangeProofGraph_computationToRight e r w hw s u i hs
  have hc : Semiformula.Evalb (M := V) ![c, a, d] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hh : Semiformula.Evalb (M := V) ![h, c]
      (proofGraphWithLogicalAxiom Th (rangeLogicalAxiomLeaf e r)).val :=
    rangeProofGraph_oneLine e r Th c
      (rangeLogicalAxiomLeaf_rangeIntro e r u i)
  have hm : Semiformula.Evalb (M := V)
      ![rangeProofValue en rn s u i, h, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th
    (rangeLogicalAxiomLeaf e r) p a c d h
      (rangeProofValue en rn s u i) hp hc hh hm

end FailureOfComposition.NumericalRangeProofs
