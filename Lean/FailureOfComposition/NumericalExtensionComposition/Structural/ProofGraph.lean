/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalExtensionComposition.Structural.Codes
public import FailureOfComposition.NumericalExtensionProofs.Structural.ProofGraph

/-!
# Exact proof graph for extension composition

The logical-axiom leaf is the accepted finite-extension leaf together with
the two new scheme leaves.  Its natural-number interpretation is exactly the
executable common checker, including malformed formula and proof codes.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalExtensionComposition

open NumericalExtensionProofs

noncomputable section

def projectionDefinednessAxiomLeaf : 𝚺₁.Semisentence 1 := .mkSigma
  (∃¹ ∃¹ ∃¹ ∃¹ projectionDefinednessAxiomCodeGraphOutputLast.val)

def componentValuesToCheckerAxiomLeaf : 𝚺₁.Semisentence 1 := .mkSigma
  (∃¹ ∃¹ ∃¹ ∃¹ ∃¹
    componentValuesToCheckerAxiomCodeGraphOutputLast.val)

theorem projectionDefinednessAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x : V) :
    Semiformula.Evalb (M := V) ![x]
        projectionDefinednessAxiomLeaf.val ↔
      ∃ a b t i : V,
        x = projectionDefinednessAxiomCodeValue a b t i := by
  have hleaf :
      Semiformula.Evalb (M := V) ![x]
          projectionDefinednessAxiomLeaf.val ↔
        ∃ i t b a : V,
          x = projectionDefinednessAxiomCodeValue a b t i := by
    simp [projectionDefinednessAxiomLeaf,
      projectionDefinednessAxiomCodeGraphOutputLast_iff]
  rw [hleaf]
  constructor
  · rintro ⟨i, t, b, a, h⟩
    exact ⟨a, b, t, i, h⟩
  · rintro ⟨a, b, t, i, h⟩
    exact ⟨i, t, b, a, h⟩

theorem componentValuesToCheckerAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x : V) :
    Semiformula.Evalb (M := V) ![x]
        componentValuesToCheckerAxiomLeaf.val ↔
      ∃ q r t c i : V,
        x = componentValuesToCheckerAxiomCodeValue q r t c i := by
  have hleaf :
      Semiformula.Evalb (M := V) ![x]
          componentValuesToCheckerAxiomLeaf.val ↔
        ∃ i c t r q : V,
          x = componentValuesToCheckerAxiomCodeValue q r t c i := by
    simp [componentValuesToCheckerAxiomLeaf,
      componentValuesToCheckerAxiomCodeGraphOutputLast_iff]
  rw [hleaf]
  constructor
  · rintro ⟨i, c, t, r, q, h⟩
    exact ⟨q, r, t, c, i, h⟩
  · rintro ⟨q, r, t, c, i, h⟩
    exact ⟨i, c, t, r, q, h⟩

def extensionCompositionLogicalAxiomLeaf : 𝚺₁.Semisentence 1 :=
  finiteExtensionLogicalAxiomLeaf ⋎
    (projectionDefinednessAxiomLeaf ⋎
      componentValuesToCheckerAxiomLeaf)

theorem extensionCompositionLogicalAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x : V) :
    Semiformula.Evalb (M := V) ![x]
        extensionCompositionLogicalAxiomLeaf.val ↔
      Semiformula.Evalb (M := V) ![x]
          finiteExtensionLogicalAxiomLeaf.val ∨
      (∃ a b t i : V,
        x = projectionDefinednessAxiomCodeValue a b t i) ∨
      (∃ q r t c i : V,
        x = componentValuesToCheckerAxiomCodeValue q r t c i) := by
  simp only [extensionCompositionLogicalAxiomLeaf,
    HierarchySymbol.Semiformula.val_or,
    LogicalConnective.HomClass.map_or]
  rw [projectionDefinednessAxiomLeaf_iff,
    componentValuesToCheckerAxiomLeaf_iff]
  simp

theorem extensionCompositionLogicalAxiomLeaf_finiteExtension
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x : V)
    (h : Semiformula.Evalb (M := V) ![x]
      finiteExtensionLogicalAxiomLeaf.val) :
    Semiformula.Evalb (M := V) ![x]
      extensionCompositionLogicalAxiomLeaf.val :=
  (extensionCompositionLogicalAxiomLeaf_iff x).mpr (Or.inl h)

theorem extensionCompositionLogicalAxiomLeaf_projectionDefinedness
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (a b t i : V) :
    Semiformula.Evalb (M := V)
      ![projectionDefinednessAxiomCodeValue a b t i]
      extensionCompositionLogicalAxiomLeaf.val :=
  (extensionCompositionLogicalAxiomLeaf_iff _).mpr
    (Or.inr (Or.inl ⟨a, b, t, i, rfl⟩))

theorem extensionCompositionLogicalAxiomLeaf_componentValuesToChecker
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r t c i : V) :
    Semiformula.Evalb (M := V)
      ![componentValuesToCheckerAxiomCodeValue q r t c i]
      extensionCompositionLogicalAxiomLeaf.val :=
  (extensionCompositionLogicalAxiomLeaf_iff _).mpr
    (Or.inr (Or.inr ⟨q, r, t, c, i, rfl⟩))

theorem extensionCompositionLogicalAxiomLeaf_nat_iff
    (w : ℕ → ℕ → Bool) (x : ℕ) :
    Semiformula.Evalb (M := ℕ) ![x]
        extensionCompositionLogicalAxiomLeaf.val ↔
      (extensionCompositionTheoryPresentation w).syn.logicalAxiom.Holds
        (decodeFormula x) := by
  rw [extensionCompositionLogicalAxiomLeaf_iff,
    finiteExtensionLogicalAxiomLeaf_nat_iff w]
  simp only [projectionDefinednessAxiomCodeValue_nat,
    componentValuesToCheckerAxiomCodeValue_nat]
  change
    (finiteExtensionLogicalAxiomTest (decodeFormula x) = true ∨
      (∃ a b t i, x = projectionDefinednessAxiomCode a b t i) ∨
      (∃ q r t c i,
        x = componentValuesToCheckerAxiomCode q r t c i)) ↔
    extensionCompositionLogicalAxiomTest (decodeFormula x) = true
  rw [finiteExtensionLogicalAxiomTest_eq_true_iff,
    extensionCompositionLogicalAxiomTest_eq_true_iff]
  unfold ExtensionCompositionLogicalAxiomShape
  rw [extensionCompositionAxiomShape_iff]
  have hcode (s : FormulaString) :
      x = encodeFormula s ↔ decodeFormula x = s := by
    constructor
    · rintro rfl
      exact decodeFormula_encodeFormula s
    · intro h
      calc
        x = encodeFormula (decodeFormula x) :=
          (encodeFormula_decodeFormula x).symm
        _ = encodeFormula s := by rw [h]
  simp only [projectionDefinednessAxiomCode,
    componentValuesToCheckerAxiomCode, hcode]

def extensionCompositionProofGraph
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝚺₁.Semisentence 2 :=
  proofGraphWithLogicalAxiom
    (extensionCompositionPRTheoryPresentation w hw)
    extensionCompositionLogicalAxiomLeaf

theorem extensionCompositionProofGraph_nat_iff
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a]
        (extensionCompositionProofGraph w hw).val ↔
      Proof_T (extensionCompositionTheoryPresentation w) p a := by
  exact proofGraphWithLogicalAxiom_nat_iff
    (extensionCompositionPRTheoryPresentation w hw)
    extensionCompositionLogicalAxiomLeaf
    (extensionCompositionLogicalAxiomLeaf_nat_iff w) p a

end

end FailureOfComposition.NumericalExtensionComposition
