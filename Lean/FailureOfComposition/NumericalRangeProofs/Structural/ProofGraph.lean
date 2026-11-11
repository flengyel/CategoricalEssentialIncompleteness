/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalRangeProofs.Structural.Codes
public import FailureOfComposition.NumericalProofBridge.Structural.ProofGraph

/-!
# Exact proof graph for the range-proof presentation

The new logical-axiom leaf checks evaluator certificates directly inside
arithmetic and includes the fixed range-introduction family for the two
external indices.  Its standard-model theorem identifies the structural graph
with the executable `Proof_T` checker, including malformed codes.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.NumericalRangeProofs

open ConcreteEvaluator NumericalProofBridge NumericalSpecialization

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

private theorem eval_fixed_range_five_iff
    {V : Type*} [ORingStructure V]
    (phi : ArithmeticSemisentence 5) (e r : ℕ) (c u i : V) :
    Semiformula.Eval
        (Semiterm.val ![i, u, c] Empty.elim ∘
          ![(#2 : ArithmeticSemiterm Empty 3), ↑e, ↑r, #1, #0])
        Empty.elim phi ↔
      Semiformula.Evalb (M := V)
        ![c, ORingStructure.numeral e, ORingStructure.numeral r, u, i]
        phi := by
  apply Iff.of_eq
  congr 2
  funext j
  fin_cases j <;> simp

/-! ## Logical-axiom leaves -/

noncomputable def computationAxiomLeaf : 𝚺₁.Semisentence 1 := .mkSigma
  “c. ∃ e s u i,
    !evalnCertificateFormula.val s e u i ∧
      !computationAxiomCodeGraph c e s u i”

theorem computationAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c : V) :
    Semiformula.Evalb (M := V) ![c] computationAxiomLeaf.val ↔
      ∃ e s u i : V,
        Semiformula.Evalb (M := V) ![s, e, u, i]
          (evalnCertificateFormula : ArithmeticSemisentence 4) ∧
        c = computationAxiomCodeValue e s u i := by
  simp [computationAxiomLeaf, eval_reversed_five_iff,
    computationAxiomCodeGraph_iff]

noncomputable def rangeIntroAxiomLeaf (e r : ℕ) : 𝚺₁.Semisentence 1 :=
  .mkSigma
    “c. ∃ u i, !rangeIntroAxiomCodeGraph c !!(e) !!(r) u i”

theorem rangeIntroAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e r : ℕ) (c : V) :
    Semiformula.Evalb (M := V) ![c] (rangeIntroAxiomLeaf e r).val ↔
      ∃ u i : V,
        c = rangeIntroAxiomCodeValue
          (ORingStructure.numeral e) (ORingStructure.numeral r) u i := by
  simp [rangeIntroAxiomLeaf, eval_fixed_range_five_iff,
    rangeIntroAxiomCodeGraph_iff]

noncomputable def rangeLogicalAxiomLeaf (e r : ℕ) : 𝚺₁.Semisentence 1 :=
  extendedLogicalAxiomLeaf ⋎
    (computationAxiomLeaf ⋎ rangeIntroAxiomLeaf e r)

theorem rangeLogicalAxiomLeaf_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e r : ℕ) (c : V) :
    Semiformula.Evalb (M := V) ![c] (rangeLogicalAxiomLeaf e r).val ↔
      Semiformula.Evalb (M := V) ![c] extendedLogicalAxiomLeaf.val ∨
      (∃ q s u i : V,
        Semiformula.Evalb (M := V) ![s, q, u, i]
          (evalnCertificateFormula : ArithmeticSemisentence 4) ∧
        c = computationAxiomCodeValue q s u i) ∨
      ∃ u i : V,
        c = rangeIntroAxiomCodeValue
          (ORingStructure.numeral e) (ORingStructure.numeral r) u i := by
  simp only [rangeLogicalAxiomLeaf,
    HierarchySymbol.Semiformula.val_or,
    LogicalConnective.HomClass.map_or]
  rw [computationAxiomLeaf_iff, rangeIntroAxiomLeaf_iff]
  simp

theorem rangeLogicalAxiomLeaf_extended
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e r : ℕ) (c : V)
    (h : Semiformula.Evalb (M := V) ![c]
      extendedLogicalAxiomLeaf.val) :
    Semiformula.Evalb (M := V) ![c]
      (rangeLogicalAxiomLeaf e r).val :=
  (rangeLogicalAxiomLeaf_iff e r c).mpr (Or.inl h)

theorem rangeLogicalAxiomLeaf_computation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e r : ℕ) (q s u i : V)
    (hs : Semiformula.Evalb (M := V) ![s, q, u, i]
      (evalnCertificateFormula : ArithmeticSemisentence 4)) :
    Semiformula.Evalb (M := V)
      ![computationAxiomCodeValue q s u i]
      (rangeLogicalAxiomLeaf e r).val :=
  (rangeLogicalAxiomLeaf_iff e r _).mpr
    (Or.inr (Or.inl ⟨q, s, u, i, hs, rfl⟩))

theorem rangeLogicalAxiomLeaf_rangeIntro
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e r : ℕ) (u i : V) :
    Semiformula.Evalb (M := V)
      ![rangeIntroAxiomCodeValue
        (ORingStructure.numeral e) (ORingStructure.numeral r) u i]
      (rangeLogicalAxiomLeaf e r).val :=
  (rangeLogicalAxiomLeaf_iff e r _).mpr
    (Or.inr (Or.inr ⟨u, i, rfl⟩))

/-! ## Standard-model checker correspondence -/

theorem rangeLogicalAxiomLeaf_nat_iff
    (e r : ℕ) (w : ℕ → ℕ → Bool) (c : ℕ) :
    Semiformula.Evalb (M := ℕ) ![c]
        (rangeLogicalAxiomLeaf e r).val ↔
      (rangeTheoryPresentation e r w).syn.logicalAxiom.Holds
        (decodeFormula c) := by
  rw [rangeLogicalAxiomLeaf_iff,
    extendedLogicalAxiomLeaf_nat_iff w]
  simp only [computationAxiomCodeValue_nat,
    rangeIntroAxiomCodeValue_nat, StringPredicate.Holds,
    extendedTheoryPresentation, rangeTheoryPresentation,
    numeral_eq_natCast_app, natCast_nat]
  change
    (extendedLogicalAxiomTest (decodeFormula c) = true ∨
      (∃ q s u i,
        stageComputation s q u i ∧ c = computationAxiomCode q s u i) ∨
      ∃ u i, c = rangeIntroAxiomCode e r u i) ↔
    rangeLogicalAxiomTest e r (decodeFormula c) = true
  rw [extendedLogicalAxiomTest_eq_true_iff,
    rangeLogicalAxiomTest_eq_true_iff]
  unfold RangeLogicalAxiomShape
  rw [computationAxiomShape_iff, rangeIntroAxiomShape_iff]
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
  simp only [computationAxiomCode, rangeIntroAxiomCode, hcode]

noncomputable def rangeProofGraph
    (e r : ℕ) (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2)) :
    𝚺₁.Semisentence 2 :=
  proofGraphWithLogicalAxiom
    (rangePRTheoryPresentation e r w hw) (rangeLogicalAxiomLeaf e r)

theorem rangeProofGraph_nat_iff
    (e r : ℕ) (w : ℕ → ℕ → Bool)
    (hw : Primrec (fun z : ℕ × ℕ => w z.1 z.2))
    (p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a]
        (rangeProofGraph e r w hw).val ↔
      Proof_T (rangeTheoryPresentation e r w) p a := by
  exact proofGraphWithLogicalAxiom_nat_iff
    (rangePRTheoryPresentation e r w hw)
    (rangeLogicalAxiomLeaf e r)
    (rangeLogicalAxiomLeaf_nat_iff e r w) p a

noncomputable def paRangeProofGraph (e r : ℕ) : 𝚺₁.Semisentence 2 :=
  rangeProofGraph e r paStageWitness primrec_paStageWitness

theorem paRangeProofGraph_nat_iff (e r p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a]
        (paRangeProofGraph e r).val ↔
      Proof_T (paRangeTheoryPresentation e r) p a := by
  exact rangeProofGraph_nat_iff e r paStageWitness
    primrec_paStageWitness p a

end FailureOfComposition.NumericalRangeProofs
