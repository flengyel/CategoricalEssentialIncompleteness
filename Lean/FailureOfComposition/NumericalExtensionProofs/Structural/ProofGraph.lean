/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalExtensionProofs.Structural.Codes
import FailureOfComposition.NumericalDomainOrder.Structural.ProofGraph

/-!
# Exact proof graph for the finite-extension presentation

The logical-axiom leaf is the accepted domain-order leaf together with the two
finite-extension scheme leaves.  Its natural-number interpretation recovers
the executable presentation exactly, including rejection of malformed formula
and proof codes.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalExtensionProofs

open NumericalDomainOrder

noncomputable section

def checkerToExtensionAxiomLeaf : 𝚺₁.Semisentence 1 := .mkSigma
  “a. ∃ c i, !checkerToExtensionAxiomCodeGraph a c i”

def extensionToCheckerAxiomLeaf : 𝚺₁.Semisentence 1 := .mkSigma
  “a. ∃ c i, !extensionToCheckerAxiomCodeGraph a c i”

theorem checkerToExtensionAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (a : V) :
    Semiformula.Evalb (M := V) ![a]
        checkerToExtensionAxiomLeaf.val ↔
      ∃ c i : V, a = checkerToExtensionAxiomCodeValue c i := by
  simp [checkerToExtensionAxiomLeaf,
    checkerToExtensionAxiomCodeGraph_iff]

theorem extensionToCheckerAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (a : V) :
    Semiformula.Evalb (M := V) ![a]
        extensionToCheckerAxiomLeaf.val ↔
      ∃ c i : V, a = extensionToCheckerAxiomCodeValue c i := by
  simp [extensionToCheckerAxiomLeaf,
    extensionToCheckerAxiomCodeGraph_iff]

def finiteExtensionLogicalAxiomLeaf : 𝚺₁.Semisentence 1 :=
  domainOrderLogicalAxiomLeaf ⋎
    (checkerToExtensionAxiomLeaf ⋎ extensionToCheckerAxiomLeaf)

theorem finiteExtensionLogicalAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (a : V) :
    Semiformula.Evalb (M := V) ![a]
        finiteExtensionLogicalAxiomLeaf.val ↔
      Semiformula.Evalb (M := V) ![a]
          domainOrderLogicalAxiomLeaf.val ∨
      (∃ c i : V, a = checkerToExtensionAxiomCodeValue c i) ∨
      (∃ c i : V, a = extensionToCheckerAxiomCodeValue c i) := by
  simp only [finiteExtensionLogicalAxiomLeaf,
    HierarchySymbol.Semiformula.val_or,
    LogicalConnective.HomClass.map_or]
  rw [checkerToExtensionAxiomLeaf_iff,
    extensionToCheckerAxiomLeaf_iff]
  simp

theorem finiteExtensionLogicalAxiomLeaf_domainOrder
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (a : V)
    (h : Semiformula.Evalb (M := V) ![a]
      domainOrderLogicalAxiomLeaf.val) :
    Semiformula.Evalb (M := V) ![a]
      finiteExtensionLogicalAxiomLeaf.val :=
  (finiteExtensionLogicalAxiomLeaf_iff a).mpr (Or.inl h)

theorem finiteExtensionLogicalAxiomLeaf_checkerToExtension
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c i : V) :
    Semiformula.Evalb (M := V)
      ![checkerToExtensionAxiomCodeValue c i]
      finiteExtensionLogicalAxiomLeaf.val :=
  (finiteExtensionLogicalAxiomLeaf_iff _).mpr
    (Or.inr (Or.inl ⟨c, i, rfl⟩))

theorem finiteExtensionLogicalAxiomLeaf_extensionToChecker
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c i : V) :
    Semiformula.Evalb (M := V)
      ![extensionToCheckerAxiomCodeValue c i]
      finiteExtensionLogicalAxiomLeaf.val :=
  (finiteExtensionLogicalAxiomLeaf_iff _).mpr
    (Or.inr (Or.inr ⟨c, i, rfl⟩))

theorem finiteExtensionLogicalAxiomLeaf_nat_iff
    (w : ℕ → ℕ → Bool) (a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![a]
        finiteExtensionLogicalAxiomLeaf.val ↔
      (finiteExtensionTheoryPresentation w).syn.logicalAxiom.Holds
        (decodeFormula a) := by
  rw [finiteExtensionLogicalAxiomLeaf_iff,
    domainOrderLogicalAxiomLeaf_nat_iff w]
  simp only [checkerToExtensionAxiomCodeValue_nat,
    extensionToCheckerAxiomCodeValue_nat]
  change
    (domainOrderLogicalAxiomTest (decodeFormula a) = true ∨
      (∃ c i, a = checkerToExtensionAxiomCode c i) ∨
      (∃ c i, a = extensionToCheckerAxiomCode c i)) ↔
    finiteExtensionLogicalAxiomTest (decodeFormula a) = true
  rw [domainOrderLogicalAxiomTest_eq_true_iff,
    finiteExtensionLogicalAxiomTest_eq_true_iff]
  unfold FiniteExtensionLogicalAxiomShape
  rw [extensionAxiomShape_iff]
  have hcode (x : FormulaString) :
      a = encodeFormula x ↔ decodeFormula a = x := by
    constructor
    · rintro rfl
      exact decodeFormula_encodeFormula x
    · intro h
      calc
        a = encodeFormula (decodeFormula a) :=
          (encodeFormula_decodeFormula a).symm
        _ = encodeFormula x := by rw [h]
  simp only [checkerToExtensionAxiomCode,
    extensionToCheckerAxiomCode, hcode]

def finiteExtensionProofGraph
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝚺₁.Semisentence 2 :=
  proofGraphWithLogicalAxiom
    (finiteExtensionPRTheoryPresentation w hw)
    finiteExtensionLogicalAxiomLeaf

theorem finiteExtensionProofGraph_nat_iff
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a]
        (finiteExtensionProofGraph w hw).val ↔
      Proof_T (finiteExtensionTheoryPresentation w) p a := by
  exact proofGraphWithLogicalAxiom_nat_iff
    (finiteExtensionPRTheoryPresentation w hw)
    finiteExtensionLogicalAxiomLeaf
    (finiteExtensionLogicalAxiomLeaf_nat_iff w) p a

end

end FailureOfComposition.NumericalExtensionProofs
