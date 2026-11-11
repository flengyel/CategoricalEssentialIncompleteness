/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalDomainOrder.Structural.ProofGraph

/-!
# Arithmetic graph of domain-order transfer

The external primitive-recursive proof transformation has an internal value
and a `𝚺₁` graph.  Two structural MP steps prove preservation for arbitrary
elements of every PA model, including nonstandard proof codes.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalDomainOrder

open NumericalProductProofs

noncomputable def domainOrderTransferValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e p s r i : V) : V :=
  mpValue
    (mpValue (oneLineProofValue (domainOrderAxiomCodeValue s r i)) e) p

noncomputable def domainOrderTransferGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “y e p s r i.
    ∃ c, !domainOrderAxiomCodeGraph c s r i ∧
    ∃ u, !oneLineProofGraph u c ∧
    ∃ v, !mpGraph v u e ∧
      !mpGraph y v p”

theorem domainOrderTransferGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y e p s r i : V) :
    Semiformula.Evalb (M := V) ![y, e, p, s, r, i]
        domainOrderTransferGraph.val ↔
      y = domainOrderTransferValue e p s r i := by
  simp [domainOrderTransferGraph, domainOrderTransferValue,
    domainOrderAxiomCodeGraph_iff, oneLineProofGraph_iff,
    mpGraph_iff_mpValue]

theorem domainOrderTransferGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e p s r i : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, e, p, s, r, i]
      domainOrderTransferGraph.val :=
  ⟨domainOrderTransferValue e p s r i,
    (domainOrderTransferGraph_iff _ _ _ _ _ _).mpr rfl⟩

theorem domainOrderTransferGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z e p s r i : V}
    (hy : Semiformula.Evalb (M := V) ![y, e, p, s, r, i]
      domainOrderTransferGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, e, p, s, r, i]
      domainOrderTransferGraph.val) :
    y = z :=
  (domainOrderTransferGraph_iff y e p s r i).mp hy |>.trans
    ((domainOrderTransferGraph_iff z e p s r i).mp hz).symm

theorem domainOrderTransferValue_nat (e p s r i : ℕ) :
    domainOrderTransferValue e p s r i =
      domainOrderTransfer e p s r i := by
  simp [domainOrderTransferValue, domainOrderTransfer,
    oneLineProofValue_nat, domainOrderAxiomCodeValue_nat, mpValue_nat]

/-! ## Internal structural preservation -/

theorem domainOrderProofGraph_oneLine
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Th : PRTheoryPresentation) (a : V)
    (ha : Semiformula.Evalb (M := V) ![a]
      domainOrderLogicalAxiomLeaf.val) :
    Semiformula.Evalb (M := V) ![oneLineProofValue a, a]
      (proofGraphWithLogicalAxiom Th domainOrderLogicalAxiomLeaf).val := by
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

theorem domainOrderProofGraph_transfer
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (e p s r i : V)
    (he : Semiformula.Evalb (M := V)
      ![e, equalityCodeValue (compIndexValue s r) r]
      (domainOrderProofGraph w hw).val)
    (hp : Semiformula.Evalb (M := V)
      ![p, rightInstanceCodeValue r i i]
      (domainOrderProofGraph w hw).val) :
    Semiformula.Evalb (M := V)
      ![domainOrderTransferValue e p s r i,
        rightInstanceCodeValue s i i]
      (domainOrderProofGraph w hw).val := by
  let Th := domainOrderPRTheoryPresentation w hw
  let a := equalityCodeValue (V := V) (compIndexValue s r) r
  let b := rightInstanceCodeValue (V := V) r i i
  let d := rightInstanceCodeValue (V := V) s i i
  let k := impValue b d
  let c := domainOrderAxiomCodeValue (V := V) s r i
  let u := oneLineProofValue c
  let v := mpValue u e
  have hc : Semiformula.Evalb (M := V) ![c, a, k] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hk : Semiformula.Evalb (M := V) ![k, b, d] impGraph.val :=
    (impGraph_iff_impValue _ _ _).mpr rfl
  have hu : Semiformula.Evalb (M := V) ![u, c]
      (proofGraphWithLogicalAxiom Th domainOrderLogicalAxiomLeaf).val :=
    domainOrderProofGraph_oneLine Th c
      (domainOrderLogicalAxiomLeaf_domainOrder s r i)
  have hm₁ : Semiformula.Evalb (M := V) ![v, u, e] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  have hv : Semiformula.Evalb (M := V) ![v, k]
      (domainOrderProofGraph w hw).val :=
    proofGraphWithLogicalAxiom_of_mpGraph Th domainOrderLogicalAxiomLeaf
      e a c k u v he hc hu hm₁
  have hm₂ : Semiformula.Evalb (M := V)
      ![domainOrderTransferValue e p s r i, v, p] mpGraph.val :=
    (mpGraph_iff_mpValue _ _ _).mpr rfl
  exact proofGraphWithLogicalAxiom_of_mpGraph Th
    domainOrderLogicalAxiomLeaf p b k d v
      (domainOrderTransferValue e p s r i) hp hk hv hm₂

end FailureOfComposition.NumericalDomainOrder
