/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalExtensionTheta.Structural.ProofGraph
public import FailureOfComposition.NumericalExtensionProofs.Structural.Maps

/-!
# Arithmetic graphs of the B1(8) proof transformations

Both proof transformations are interpreted on arbitrary PA-model elements.
The structural correctness theorems use the same theta proof graph for input
and output predicates and therefore cover nonstandard proof and program-index
codes.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalExtensionTheta

open NumericalExtensionComposition NumericalExtensionProofs

noncomputable section

private theorem eval_select_theta_axiom_iff
    {V : Type*} [ORingStructure V]
    (phi : ArithmeticSemisentence 5)
    (x y p s q t c i : V) :
    Semiformula.Eval
        (Semiterm.val ![x, y, p, s, q, t, c, i] Empty.elim ∘
          ![(#0 : ArithmeticSemiterm Empty 8), #4, #5, #6, #7])
        Empty.elim phi ↔
      Semiformula.Evalb (M := V) ![x, q, t, c, i] phi := by
  apply Iff.of_eq
  congr 2
  funext j
  fin_cases j <;> rfl

private theorem eval_select_checker_theta_map_iff
    {V : Type*} [ORingStructure V]
    (phi : ArithmeticSemisentence 7)
    (d y p s q t c i : V) :
    Semiformula.Eval
        (Semiterm.val ![d, y, p, s, q, t, c, i] Empty.elim ∘
          ![(#1 : ArithmeticSemiterm Empty 8), #2, #0, #4, #5, #6, #7])
        Empty.elim phi ↔
      Semiformula.Evalb (M := V) ![y, p, d, q, t, c, i] phi := by
  apply Iff.of_eq
  congr 2
  funext j
  fin_cases j <;> rfl

/-! ## Internal values and graphs -/

def componentAndCheckerToThetaValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p s q t c i : V) : V :=
  mpValue
    (mpValue (oneLineProofValue
      (componentAndCheckerToThetaAxiomCodeValue q t c i)) p) s

def componentAndExtToThetaValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p s q t c i : V) : V :=
  componentAndCheckerToThetaValue p (extToCheckerValue s c i)
    q t c i

def componentAndCheckerToThetaGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “y p s q t c i.
    ∃ k, !componentAndCheckerToThetaAxiomCodeGraph k q t c i ∧
    ∃ a, !oneLineProofGraph a k ∧
    ∃ b, !mpGraph b a p ∧
      !mpGraph y b s”

def componentAndExtToThetaGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “y p s q t c i.
    ∃ d, !extToCheckerGraph d s c i ∧
      !componentAndCheckerToThetaGraph y p d q t c i”

theorem componentAndCheckerToThetaGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y p s q t c i : V) :
    Semiformula.Evalb (M := V) ![y, p, s, q, t, c, i]
        componentAndCheckerToThetaGraph.val ↔
      y = componentAndCheckerToThetaValue p s q t c i := by
  simp [componentAndCheckerToThetaGraph,
    componentAndCheckerToThetaValue, eval_select_theta_axiom_iff,
    componentAndCheckerToThetaAxiomCodeGraph_iff,
    oneLineProofGraph_iff, mpGraph_iff_mpValue]

theorem componentAndExtToThetaGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y p s q t c i : V) :
    Semiformula.Evalb (M := V) ![y, p, s, q, t, c, i]
        componentAndExtToThetaGraph.val ↔
      y = componentAndExtToThetaValue p s q t c i := by
  simp [componentAndExtToThetaGraph, componentAndExtToThetaValue,
    eval_select_checker_theta_map_iff, extToCheckerGraph_iff,
    componentAndCheckerToThetaGraph_iff]

/-! ## Totality and functionality -/

theorem componentAndCheckerToThetaGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p s q t c i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, p, s, q, t, c, i]
      componentAndCheckerToThetaGraph.val :=
  ⟨componentAndCheckerToThetaValue p s q t c i,
    (componentAndCheckerToThetaGraph_iff _ _ _ _ _ _ _).mpr rfl⟩

theorem componentAndExtToThetaGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (p s q t c i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, p, s, q, t, c, i]
      componentAndExtToThetaGraph.val :=
  ⟨componentAndExtToThetaValue p s q t c i,
    (componentAndExtToThetaGraph_iff _ _ _ _ _ _ _).mpr rfl⟩

theorem componentAndCheckerToThetaGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z p s q t c i : V}
    (hy : Semiformula.Evalb (M := V) ![y, p, s, q, t, c, i]
      componentAndCheckerToThetaGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, p, s, q, t, c, i]
      componentAndCheckerToThetaGraph.val) : y = z :=
  (componentAndCheckerToThetaGraph_iff y p s q t c i).mp hy |>.trans
    ((componentAndCheckerToThetaGraph_iff z p s q t c i).mp hz).symm

theorem componentAndExtToThetaGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z p s q t c i : V}
    (hy : Semiformula.Evalb (M := V) ![y, p, s, q, t, c, i]
      componentAndExtToThetaGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, p, s, q, t, c, i]
      componentAndExtToThetaGraph.val) : y = z :=
  (componentAndExtToThetaGraph_iff y p s q t c i).mp hy |>.trans
    ((componentAndExtToThetaGraph_iff z p s q t c i).mp hz).symm

/-! ## Standard-natural-number values -/

theorem componentAndCheckerToThetaValue_nat
    (p s q t c i : ℕ) :
    componentAndCheckerToThetaValue p s q t c i =
      componentAndCheckerToTheta p s q t c i := by
  simp [componentAndCheckerToThetaValue, componentAndCheckerToTheta,
    componentAndCheckerToThetaAxiomCodeValue_nat,
    oneLineProofValue_nat, mpValue_nat]

theorem componentAndExtToThetaValue_nat
    (p s q t c i : ℕ) :
    componentAndExtToThetaValue p s q t c i =
      componentAndExtToTheta p s q t c i := by
  simp [componentAndExtToThetaValue, componentAndExtToTheta,
    componentAndCheckerToThetaValue_nat, extToCheckerValue_nat]

/-! ## Internal structural preservation -/

theorem extensionThetaProofGraph_oneLine
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Th : PRTheoryPresentation) (a : V)
    (ha : Semiformula.Evalb (M := V) ![a]
      extensionThetaLogicalAxiomLeaf.val) :
    Semiformula.Evalb (M := V) ![oneLineProofValue a, a]
      (proofGraphWithLogicalAxiom Th
        extensionThetaLogicalAxiomLeaf).val := by
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

private theorem extensionThetaLogicalAxiomLeaf_extensionToChecker
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c i : V) :
    Semiformula.Evalb (M := V)
      ![extensionToCheckerAxiomCodeValue c i]
      extensionThetaLogicalAxiomLeaf.val := by
  apply extensionThetaLogicalAxiomLeaf_extensionComposition
  apply extensionCompositionLogicalAxiomLeaf_finiteExtension
  exact finiteExtensionLogicalAxiomLeaf_extensionToChecker c i

theorem extensionThetaProofGraph_extToChecker
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p c i : V)
    (hp : Semiformula.Evalb (M := V)
      ![p, extensionInstanceCodeValue c i]
      (extensionThetaProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![extToCheckerValue p c i, checkerInstanceCodeValue c i]
      (extensionThetaProofGraph w hw).val := by
  let Th := extensionThetaPRTheoryPresentation w hw
  let a := extensionInstanceCodeValue (V := V) c i
  let b := checkerInstanceCodeValue (V := V) c i
  let k := extensionToCheckerAxiomCodeValue (V := V) c i
  let s := oneLineProofValue k
  have hk : Semiformula.Evalb (M := V) ![k, a, b] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hs : Semiformula.Evalb (M := V) ![s, k]
      (proofGraphWithLogicalAxiom Th
        extensionThetaLogicalAxiomLeaf).val :=
    extensionThetaProofGraph_oneLine Th k
      (extensionThetaLogicalAxiomLeaf_extensionToChecker c i)
  have hm : Semiformula.Evalb (M := V)
      ![extToCheckerValue p c i, s, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th
    extensionThetaLogicalAxiomLeaf p a k b s
      (extToCheckerValue p c i) hp hk hs hm

theorem extensionThetaProofGraph_componentAndCheckerToTheta
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p s q t c i : V)
    (hp : Semiformula.Evalb (M := V)
      ![p, rightInstanceCodeValue q t c]
      (extensionThetaProofGraph w hw).val)
    (hs : Semiformula.Evalb (M := V)
      ![s, checkerInstanceCodeValue c i]
      (extensionThetaProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![componentAndCheckerToThetaValue p s q t c i,
        thetaInstanceCodeValue q t i]
      (extensionThetaProofGraph w hw).val := by
  let Th := extensionThetaPRTheoryPresentation w hw
  let a := rightInstanceCodeValue (V := V) q t c
  let b := checkerInstanceCodeValue (V := V) c i
  let h := thetaInstanceCodeValue (V := V) q t i
  let l := impValue b h
  let k := componentAndCheckerToThetaAxiomCodeValue (V := V) q t c i
  let u := oneLineProofValue k
  let v := mpValue u p
  have hk₁ : Semiformula.Evalb (M := V) ![k, a, l] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hk₂ : Semiformula.Evalb (M := V) ![l, b, h] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hu : Semiformula.Evalb (M := V) ![u, k]
      (proofGraphWithLogicalAxiom Th
        extensionThetaLogicalAxiomLeaf).val :=
    extensionThetaProofGraph_oneLine Th k
      (extensionThetaLogicalAxiomLeaf_componentAndCheckerToTheta q t c i)
  have hmp₁ : Semiformula.Evalb (M := V) ![v, u, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  have hv : Semiformula.Evalb (M := V) ![v, l]
      (extensionThetaProofGraph w hw).val :=
    proofGraphWithLogicalAxiom_of_mpGraph Th
      extensionThetaLogicalAxiomLeaf p a k l u v hp hk₁ hu hmp₁
  have hmp₂ : Semiformula.Evalb (M := V)
      ![componentAndCheckerToThetaValue p s q t c i, v, s]
      mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th
    extensionThetaLogicalAxiomLeaf s b l h v
      (componentAndCheckerToThetaValue p s q t c i)
      hs hk₂ hv hmp₂

theorem extensionThetaProofGraph_componentAndExtToTheta
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p s q t c i : V)
    (hp : Semiformula.Evalb (M := V)
      ![p, rightInstanceCodeValue q t c]
      (extensionThetaProofGraph w hw).val)
    (hs : Semiformula.Evalb (M := V)
      ![s, extensionInstanceCodeValue c i]
      (extensionThetaProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![componentAndExtToThetaValue p s q t c i,
        thetaInstanceCodeValue q t i]
      (extensionThetaProofGraph w hw).val :=
  extensionThetaProofGraph_componentAndCheckerToTheta w hw
    p (extToCheckerValue s c i) q t c i hp
      (extensionThetaProofGraph_extToChecker w hw s c i hs)

end

end FailureOfComposition.NumericalExtensionTheta
