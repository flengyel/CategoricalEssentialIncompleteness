/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalProductProofs.Structural.Codes

/-!
# Exact proof graph for the product presentation

The logical-axiom leaf extends the accepted bridge leaf by exactly the five
product-definedness schemas.  Over the standard natural numbers, the resulting
structural proof graph is equivalent to the executable proof predicate.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.NumericalProductProofs

open ProofSearch ConcreteEvaluator NumericalProofBridge

noncomputable def project0ToPairAxiomLeaf : 𝚺₁.Semisentence 1 := .mkSigma
  “c. ∃ q r n, !project0ToPairAxiomCodeGraph c q r n”

noncomputable def project1ToPairAxiomLeaf : 𝚺₁.Semisentence 1 := .mkSigma
  “c. ∃ q r n, !project1ToPairAxiomCodeGraph c q r n”

noncomputable def pairToLeftAxiomLeaf : 𝚺₁.Semisentence 1 := .mkSigma
  “c. ∃ q r n, !pairToLeftAxiomCodeGraph c q r n”

noncomputable def pairToRightAxiomLeaf : 𝚺₁.Semisentence 1 := .mkSigma
  “c. ∃ q r n, !pairToRightAxiomCodeGraph c q r n”

noncomputable def componentsToPairAxiomLeaf : 𝚺₁.Semisentence 1 := .mkSigma
  “c. ∃ q r n, !componentsToPairAxiomCodeGraph c q r n”

theorem project0ToPairAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c : V) :
    Semiformula.Evalb (M := V) ![c] project0ToPairAxiomLeaf.val ↔
      ∃ q r n : V, c = project0ToPairAxiomCodeValue q r n := by
  simp [project0ToPairAxiomLeaf,
    project0ToPairAxiomCodeGraph_iff]

theorem project1ToPairAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c : V) :
    Semiformula.Evalb (M := V) ![c] project1ToPairAxiomLeaf.val ↔
      ∃ q r n : V, c = project1ToPairAxiomCodeValue q r n := by
  simp [project1ToPairAxiomLeaf,
    project1ToPairAxiomCodeGraph_iff]

theorem pairToLeftAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c : V) :
    Semiformula.Evalb (M := V) ![c] pairToLeftAxiomLeaf.val ↔
      ∃ q r n : V, c = pairToLeftAxiomCodeValue q r n := by
  simp [pairToLeftAxiomLeaf,
    pairToLeftAxiomCodeGraph_iff]

theorem pairToRightAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c : V) :
    Semiformula.Evalb (M := V) ![c] pairToRightAxiomLeaf.val ↔
      ∃ q r n : V, c = pairToRightAxiomCodeValue q r n := by
  simp [pairToRightAxiomLeaf,
    pairToRightAxiomCodeGraph_iff]

theorem componentsToPairAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c : V) :
    Semiformula.Evalb (M := V) ![c] componentsToPairAxiomLeaf.val ↔
      ∃ q r n : V, c = componentsToPairAxiomCodeValue q r n := by
  simp [componentsToPairAxiomLeaf,
    componentsToPairAxiomCodeGraph_iff]

noncomputable def productLogicalAxiomLeaf : 𝚺₁.Semisentence 1 :=
  extendedLogicalAxiomLeaf ⋎
    (project0ToPairAxiomLeaf ⋎
      (project1ToPairAxiomLeaf ⋎
        (pairToLeftAxiomLeaf ⋎
          (pairToRightAxiomLeaf ⋎ componentsToPairAxiomLeaf))))

theorem productLogicalAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c : V) :
    Semiformula.Evalb (M := V) ![c] productLogicalAxiomLeaf.val ↔
      Semiformula.Evalb (M := V) ![c] extendedLogicalAxiomLeaf.val ∨
      (∃ q r n : V, c = project0ToPairAxiomCodeValue q r n) ∨
      (∃ q r n : V, c = project1ToPairAxiomCodeValue q r n) ∨
      (∃ q r n : V, c = pairToLeftAxiomCodeValue q r n) ∨
      (∃ q r n : V, c = pairToRightAxiomCodeValue q r n) ∨
      (∃ q r n : V, c = componentsToPairAxiomCodeValue q r n) := by
  simp only [productLogicalAxiomLeaf,
    HierarchySymbol.Semiformula.val_or,
    LogicalConnective.HomClass.map_or]
  rw [project0ToPairAxiomLeaf_iff, project1ToPairAxiomLeaf_iff,
    pairToLeftAxiomLeaf_iff, pairToRightAxiomLeaf_iff,
    componentsToPairAxiomLeaf_iff]
  rfl

theorem productLogicalAxiomLeaf_old
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c : V)
    (h : Semiformula.Evalb (M := V) ![c]
      extendedLogicalAxiomLeaf.val) :
    Semiformula.Evalb (M := V) ![c] productLogicalAxiomLeaf.val :=
  (productLogicalAxiomLeaf_iff c).mpr (Or.inl h)

theorem productLogicalAxiomLeaf_project0ToPair
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r n : V) :
    Semiformula.Evalb (M := V)
      ![project0ToPairAxiomCodeValue q r n]
      productLogicalAxiomLeaf.val :=
  (productLogicalAxiomLeaf_iff _).mpr
    (Or.inr (Or.inl ⟨q, r, n, rfl⟩))

theorem productLogicalAxiomLeaf_project1ToPair
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r n : V) :
    Semiformula.Evalb (M := V)
      ![project1ToPairAxiomCodeValue q r n]
      productLogicalAxiomLeaf.val :=
  (productLogicalAxiomLeaf_iff _).mpr
    (Or.inr (Or.inr (Or.inl ⟨q, r, n, rfl⟩)))

theorem productLogicalAxiomLeaf_pairToLeft
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r n : V) :
    Semiformula.Evalb (M := V)
      ![pairToLeftAxiomCodeValue q r n]
      productLogicalAxiomLeaf.val :=
  (productLogicalAxiomLeaf_iff _).mpr
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, r, n, rfl⟩))))

theorem productLogicalAxiomLeaf_pairToRight
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r n : V) :
    Semiformula.Evalb (M := V)
      ![pairToRightAxiomCodeValue q r n]
      productLogicalAxiomLeaf.val :=
  (productLogicalAxiomLeaf_iff _).mpr
    (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨q, r, n, rfl⟩)))))

theorem productLogicalAxiomLeaf_componentsToPair
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r n : V) :
    Semiformula.Evalb (M := V)
      ![componentsToPairAxiomCodeValue q r n]
      productLogicalAxiomLeaf.val :=
  (productLogicalAxiomLeaf_iff _).mpr
    (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨q, r, n, rfl⟩)))))

theorem productLogicalAxiomLeaf_nat_iff
    (w : ℕ → ℕ → Bool) (c : ℕ) :
    Semiformula.Evalb (M := ℕ) ![c] productLogicalAxiomLeaf.val ↔
      (productTheoryPresentation w).syn.logicalAxiom.Holds
        (decodeFormula c) := by
  rw [productLogicalAxiomLeaf_iff,
    extendedLogicalAxiomLeaf_nat_iff w]
  simp only [project0ToPairAxiomCodeValue_nat,
    project1ToPairAxiomCodeValue_nat, pairToLeftAxiomCodeValue_nat,
    pairToRightAxiomCodeValue_nat, componentsToPairAxiomCodeValue_nat]
  change
    (extendedLogicalAxiomTest (decodeFormula c) = true ∨
      (∃ q r n, c = project0ToPairAxiomCode q r n) ∨
      (∃ q r n, c = project1ToPairAxiomCode q r n) ∨
      (∃ q r n, c = pairToLeftAxiomCode q r n) ∨
      (∃ q r n, c = pairToRightAxiomCode q r n) ∨
      (∃ q r n, c = componentsToPairAxiomCode q r n)) ↔
    productLogicalAxiomTest (decodeFormula c) = true
  rw [extendedLogicalAxiomTest_eq_true_iff,
    productLogicalAxiomTest_eq_true_iff]
  unfold ProductLogicalAxiomShape
  rw [productAxiomShape_iff]
  have hcode (t : FormulaString) :
      c = encodeFormula t ↔ decodeFormula c = t := by
    constructor
    · rintro rfl
      exact decodeFormula_encodeFormula t
    · intro h
      calc
        c = encodeFormula (decodeFormula c) :=
          (encodeFormula_decodeFormula c).symm
        _ = encodeFormula t := by rw [h]
  simp only [project0ToPairAxiomCode, project1ToPairAxiomCode,
    pairToLeftAxiomCode, pairToRightAxiomCode,
    componentsToPairAxiomCode, hcode]

noncomputable def productProofGraph
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝚺₁.Semisentence 2 :=
  proofGraphWithLogicalAxiom
    (productPRTheoryPresentation w hw) productLogicalAxiomLeaf

theorem productProofGraph_nat_iff
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a]
        (productProofGraph w hw).val ↔
      Proof_T (productTheoryPresentation w) p a := by
  exact proofGraphWithLogicalAxiom_nat_iff
    (productPRTheoryPresentation w hw)
    productLogicalAxiomLeaf
    (productLogicalAxiomLeaf_nat_iff w) p a

end FailureOfComposition.NumericalProductProofs
