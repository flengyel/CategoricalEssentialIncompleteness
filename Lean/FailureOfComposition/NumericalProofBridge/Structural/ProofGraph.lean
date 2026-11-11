/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalProofBridge.Structural.AxiomCodes

/-!
# Exact structural proof graph for the extended presentation
-/

@[expose] public section

set_option autoImplicit false
open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural
open Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator
open FailureOfComposition.NumericalSpecialization

namespace FailureOfComposition.NumericalProofBridge

open ProofSearch ConcreteEvaluator

private theorem eval_reversed_five_iff
    {V : Type*} [ORingStructure V]
    (phi : ArithmeticSemisentence 5) (a b c d e : V) :
    Semiformula.Eval
        (Semiterm.val ![e, d, c, b, a] Empty.elim ∘
          ![(#4 : ArithmeticSemiterm Empty 5), #3, #2, #1, #0])
        Empty.elim phi ↔
      Semiformula.Evalb (M := V) ![a, b, c, d, e] phi := by
  apply Iff.of_eq
  congr 2
  funext j
  fin_cases j <;> rfl

noncomputable def extendedLogicalAxiomLeaf : 𝚺₁.Semisentence 1 := .mkSigma
  “c.
    !specializationLogicalAxiomLeaf c ∨
    (∃ q r s, !bridgeEqualityAxiomCodeGraph c q r s) ∨
    (∃ q n m s, !bridgeLeftAxiomCodeGraph c q n m s) ∨
    (∃ r n m s, !bridgeRightAxiomCodeGraph c r n m s)”

theorem extendedLogicalAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c : V) :
    Semiformula.Evalb (M := V) ![c] extendedLogicalAxiomLeaf.val ↔
      Semiformula.Evalb (M := V) ![c]
        specializationLogicalAxiomLeaf.val ∨
      (∃ q r s : V, c = bridgeEqualityAxiomCodeValue q r s) ∨
      (∃ q n m s : V, c = bridgeLeftAxiomCodeValue q n m s) ∨
      (∃ r n m s : V, c = bridgeRightAxiomCodeValue r n m s) := by
  simp [extendedLogicalAxiomLeaf, bridgeEqualityAxiomCodeGraph_iff,
    eval_reversed_five_iff, bridgeLeftAxiomCodeGraph_iff,
    bridgeRightAxiomCodeGraph_iff]

theorem extendedLogicalAxiomLeaf_old
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (c : V)
    (h : Semiformula.Evalb (M := V) ![c]
      specializationLogicalAxiomLeaf.val) :
    Semiformula.Evalb (M := V) ![c] extendedLogicalAxiomLeaf.val :=
  (extendedLogicalAxiomLeaf_iff c).mpr (Or.inl h)

theorem extendedLogicalAxiomLeaf_bridgeEquality
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r s : V) :
    Semiformula.Evalb (M := V)
      ![bridgeEqualityAxiomCodeValue q r s]
      extendedLogicalAxiomLeaf.val :=
  (extendedLogicalAxiomLeaf_iff _).mpr
    (Or.inr (Or.inl ⟨q, r, s, rfl⟩))

theorem extendedLogicalAxiomLeaf_bridgeLeft
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q n m s : V) :
    Semiformula.Evalb (M := V)
      ![bridgeLeftAxiomCodeValue q n m s]
      extendedLogicalAxiomLeaf.val :=
  (extendedLogicalAxiomLeaf_iff _).mpr
    (Or.inr (Or.inr (Or.inl ⟨q, n, m, s, rfl⟩)))

theorem extendedLogicalAxiomLeaf_bridgeRight
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (r n m s : V) :
    Semiformula.Evalb (M := V)
      ![bridgeRightAxiomCodeValue r n m s]
      extendedLogicalAxiomLeaf.val :=
  (extendedLogicalAxiomLeaf_iff _).mpr
    (Or.inr (Or.inr (Or.inr ⟨r, n, m, s, rfl⟩)))

theorem extendedLogicalAxiomLeaf_nat_iff
    (w : ℕ → ℕ → Bool) (c : ℕ) :
    Semiformula.Evalb (M := ℕ) ![c] extendedLogicalAxiomLeaf.val ↔
      (extendedTheoryPresentation w).syn.logicalAxiom.Holds
        (decodeFormula c) := by
  rw [extendedLogicalAxiomLeaf_iff,
    specializationLogicalAxiomLeaf_nat_iff w]
  simp only [bridgeEqualityAxiomCodeValue_nat,
    bridgeLeftAxiomCodeValue_nat, bridgeRightAxiomCodeValue_nat]
  change
    (logicalAxiomTest (decodeFormula c) = true ∨
      (∃ q r s, c = bridgeEqualityAxiomCode q r s) ∨
      (∃ q n m s, c = bridgeLeftAxiomCode q n m s) ∨
      (∃ r n m s, c = bridgeRightAxiomCode r n m s)) ↔
    extendedLogicalAxiomTest (decodeFormula c) = true
  rw [logicalAxiomTest_eq_true_iff,
    extendedLogicalAxiomTest_eq_true_iff]
  unfold ExtendedLogicalAxiomShape
  rw [bridgeAxiomShape_iff]
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
  simp only [bridgeEqualityAxiomCode, bridgeLeftAxiomCode,
    bridgeRightAxiomCode, hcode]

noncomputable def extendedProofGraph
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝚺₁.Semisentence 2 :=
  proofGraphWithLogicalAxiom
    (extendedPRTheoryPresentation w hw) extendedLogicalAxiomLeaf

theorem extendedProofGraph_nat_iff
    (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a]
        (extendedProofGraph w hw).val ↔
      Proof_T (extendedTheoryPresentation w) p a := by
  exact proofGraphWithLogicalAxiom_nat_iff
    (extendedPRTheoryPresentation w hw)
    extendedLogicalAxiomLeaf
    (extendedLogicalAxiomLeaf_nat_iff w) p a

noncomputable def paExtendedProofGraph : 𝚺₁.Semisentence 2 :=
  extendedProofGraph paStageWitness primrec_paStageWitness

theorem paExtendedProofGraph_nat_iff (p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a] paExtendedProofGraph.val ↔
      Proof_T paExtendedTheoryPresentation p a := by
  exact extendedProofGraph_nat_iff
    paStageWitness primrec_paStageWitness p a

end FailureOfComposition.NumericalProofBridge
