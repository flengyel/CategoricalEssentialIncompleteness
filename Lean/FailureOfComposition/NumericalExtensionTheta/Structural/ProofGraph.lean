/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalExtensionTheta.Structural.Codes
import FailureOfComposition.NumericalExtensionComposition.Structural.ProofGraph

/-!
# Exact proof graph for the B1(8) common checker

The logical-axiom leaf is the accepted extension-composition leaf together
with the one theta-scheme leaf.  Its natural-number interpretation agrees
exactly with the executable presentation, including malformed formula and
proof codes.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.NumericalExtensionTheta

open NumericalExtensionComposition

noncomputable section

def componentAndCheckerToThetaAxiomLeaf : 𝚺₁.Semisentence 1 := .mkSigma
  (∃¹ ∃¹ ∃¹ ∃¹
    componentAndCheckerToThetaAxiomCodeGraphOutputLast.val)

theorem componentAndCheckerToThetaAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x : V) :
    Semiformula.Evalb (M := V) ![x]
        componentAndCheckerToThetaAxiomLeaf.val ↔
      ∃ q t c i : V,
        x = componentAndCheckerToThetaAxiomCodeValue q t c i := by
  have hleaf :
      Semiformula.Evalb (M := V) ![x]
          componentAndCheckerToThetaAxiomLeaf.val ↔
        ∃ i c t q : V,
          x = componentAndCheckerToThetaAxiomCodeValue q t c i := by
    simp [componentAndCheckerToThetaAxiomLeaf,
      componentAndCheckerToThetaAxiomCodeGraphOutputLast_iff]
  rw [hleaf]
  constructor
  · rintro ⟨i, c, t, q, h⟩
    exact ⟨q, t, c, i, h⟩
  · rintro ⟨q, t, c, i, h⟩
    exact ⟨i, c, t, q, h⟩

def extensionThetaLogicalAxiomLeaf : 𝚺₁.Semisentence 1 :=
  extensionCompositionLogicalAxiomLeaf ⋎
    componentAndCheckerToThetaAxiomLeaf

theorem extensionThetaLogicalAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x : V) :
    Semiformula.Evalb (M := V) ![x]
        extensionThetaLogicalAxiomLeaf.val ↔
      Semiformula.Evalb (M := V) ![x]
          extensionCompositionLogicalAxiomLeaf.val ∨
      ∃ q t c i : V,
        x = componentAndCheckerToThetaAxiomCodeValue q t c i := by
  simp only [extensionThetaLogicalAxiomLeaf,
    HierarchySymbol.Semiformula.val_or,
    LogicalConnective.HomClass.map_or]
  rw [componentAndCheckerToThetaAxiomLeaf_iff]
  simp

theorem extensionThetaLogicalAxiomLeaf_extensionComposition
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x : V)
    (h : Semiformula.Evalb (M := V) ![x]
      extensionCompositionLogicalAxiomLeaf.val) :
    Semiformula.Evalb (M := V) ![x]
      extensionThetaLogicalAxiomLeaf.val :=
  (extensionThetaLogicalAxiomLeaf_iff x).mpr (Or.inl h)

theorem extensionThetaLogicalAxiomLeaf_componentAndCheckerToTheta
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q t c i : V) :
    Semiformula.Evalb (M := V)
      ![componentAndCheckerToThetaAxiomCodeValue q t c i]
      extensionThetaLogicalAxiomLeaf.val :=
  (extensionThetaLogicalAxiomLeaf_iff _).mpr
    (Or.inr ⟨q, t, c, i, rfl⟩)

theorem extensionThetaLogicalAxiomLeaf_nat_iff
    (w : ℕ → ℕ → Bool) (x : ℕ) :
    Semiformula.Evalb (M := ℕ) ![x]
        extensionThetaLogicalAxiomLeaf.val ↔
      (extensionThetaTheoryPresentation w).syn.logicalAxiom.Holds
        (decodeFormula x) := by
  rw [extensionThetaLogicalAxiomLeaf_iff,
    extensionCompositionLogicalAxiomLeaf_nat_iff w]
  simp only [componentAndCheckerToThetaAxiomCodeValue_nat]
  change
    (extensionCompositionLogicalAxiomTest (decodeFormula x) = true ∨
      ∃ q t c i,
        x = componentAndCheckerToThetaAxiomCode q t c i) ↔
      extensionThetaLogicalAxiomTest (decodeFormula x) = true
  rw [extensionCompositionLogicalAxiomTest_eq_true_iff,
    extensionThetaLogicalAxiomTest_eq_true_iff]
  unfold ExtensionThetaLogicalAxiomShape
  rw [extensionThetaAxiomShape_iff]
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
  simp only [componentAndCheckerToThetaAxiomCode, hcode]

def extensionThetaProofGraph
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝚺₁.Semisentence 2 :=
  proofGraphWithLogicalAxiom
    (extensionThetaPRTheoryPresentation w hw)
    extensionThetaLogicalAxiomLeaf

theorem extensionThetaProofGraph_nat_iff
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a]
        (extensionThetaProofGraph w hw).val ↔
      Proof_T (extensionThetaTheoryPresentation w) p a := by
  exact proofGraphWithLogicalAxiom_nat_iff
    (extensionThetaPRTheoryPresentation w hw)
    extensionThetaLogicalAxiomLeaf
    (extensionThetaLogicalAxiomLeaf_nat_iff w) p a

end

end FailureOfComposition.NumericalExtensionTheta
