/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalDomainOrder.Structural.Codes
import FailureOfComposition.NumericalProductProofs.Structural.ProofGraph

/-!
# Exact proof graph for the domain-order presentation

The logical-axiom leaf is the disjunction of the accepted product leaf and the
single domain-order leaf.  Its standard-natural-number theorem identifies the
resulting structural graph with the executable `Proof_T` predicate, including
malformed proof and formula codes.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalDomainOrder

open NumericalProductProofs

noncomputable def domainOrderAxiomLeaf : 𝚺₁.Semisentence 1 := .mkSigma
  “c. ∃ s r i, !domainOrderAxiomCodeGraph c s r i”

theorem domainOrderAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c : V) :
    Semiformula.Evalb (M := V) ![c] domainOrderAxiomLeaf.val ↔
      ∃ s r i : V, c = domainOrderAxiomCodeValue s r i := by
  simp [domainOrderAxiomLeaf, domainOrderAxiomCodeGraph_iff]

noncomputable def domainOrderLogicalAxiomLeaf : 𝚺₁.Semisentence 1 :=
  productLogicalAxiomLeaf ⋎ domainOrderAxiomLeaf

theorem domainOrderLogicalAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c : V) :
    Semiformula.Evalb (M := V) ![c] domainOrderLogicalAxiomLeaf.val ↔
      Semiformula.Evalb (M := V) ![c] productLogicalAxiomLeaf.val ∨
      ∃ s r i : V, c = domainOrderAxiomCodeValue s r i := by
  simp only [domainOrderLogicalAxiomLeaf,
    HierarchySymbol.Semiformula.val_or,
    LogicalConnective.HomClass.map_or]
  rw [domainOrderAxiomLeaf_iff]
  simp

theorem domainOrderLogicalAxiomLeaf_product
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c : V)
    (h : Semiformula.Evalb (M := V) ![c]
      productLogicalAxiomLeaf.val) :
    Semiformula.Evalb (M := V) ![c]
      domainOrderLogicalAxiomLeaf.val :=
  (domainOrderLogicalAxiomLeaf_iff c).mpr (Or.inl h)

theorem domainOrderLogicalAxiomLeaf_domainOrder
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (s r i : V) :
    Semiformula.Evalb (M := V)
      ![domainOrderAxiomCodeValue s r i]
      domainOrderLogicalAxiomLeaf.val :=
  (domainOrderLogicalAxiomLeaf_iff _).mpr
    (Or.inr ⟨s, r, i, rfl⟩)

theorem domainOrderLogicalAxiomLeaf_nat_iff
    (w : ℕ → ℕ → Bool) (c : ℕ) :
    Semiformula.Evalb (M := ℕ) ![c]
        domainOrderLogicalAxiomLeaf.val ↔
      (domainOrderTheoryPresentation w).syn.logicalAxiom.Holds
        (decodeFormula c) := by
  rw [domainOrderLogicalAxiomLeaf_iff,
    productLogicalAxiomLeaf_nat_iff w]
  simp only [domainOrderAxiomCodeValue_nat]
  change
    (productLogicalAxiomTest (decodeFormula c) = true ∨
      ∃ s r i, c = domainOrderAxiomCode s r i) ↔
    domainOrderLogicalAxiomTest (decodeFormula c) = true
  rw [productLogicalAxiomTest_eq_true_iff,
    domainOrderLogicalAxiomTest_eq_true_iff]
  unfold DomainOrderLogicalAxiomShape
  rw [domainOrderAxiomShape_iff]
  have hcode (x : FormulaString) :
      c = encodeFormula x ↔ decodeFormula c = x := by
    constructor
    · rintro rfl
      exact decodeFormula_encodeFormula x
    · intro h
      calc
        c = encodeFormula (decodeFormula c) :=
          (encodeFormula_decodeFormula c).symm
        _ = encodeFormula x := by rw [h]
  simp only [domainOrderAxiomCode, hcode]

noncomputable def domainOrderProofGraph
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝚺₁.Semisentence 2 :=
  proofGraphWithLogicalAxiom
    (domainOrderPRTheoryPresentation w hw) domainOrderLogicalAxiomLeaf

theorem domainOrderProofGraph_nat_iff
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a]
        (domainOrderProofGraph w hw).val ↔
      Proof_T (domainOrderTheoryPresentation w) p a := by
  exact proofGraphWithLogicalAxiom_nat_iff
    (domainOrderPRTheoryPresentation w hw)
    domainOrderLogicalAxiomLeaf
    (domainOrderLogicalAxiomLeaf_nat_iff w) p a

end FailureOfComposition.NumericalDomainOrder
