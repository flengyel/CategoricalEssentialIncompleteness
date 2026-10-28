/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NumericalRangeProofs.Structural.Maps

/-!
# PA-internal preservation for the range proof map

The source and range indices are fixed external parameters.  The evaluator
stage, input, output, endpoint formula code, and produced proof code are all
quantified inside arithmetic.  This is the fixed-parameter uniformity required
by B1(4); it does not assert an internal or primitive-recursive selector of a
range index from a source index.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.NumericalRangeProofs

open NumericalProofBridge NumericalSpecialization

noncomputable def rangeProofPreservationMatrix (e r : ℕ) :
    ArithmeticSemisentence 5 :=
  “s u i d p.
    !rightInstanceCodeGraph d !!(r) i i ∧
    !rangeProofMapGraph p !!(e) !!(r) s u i ∧
    !evalnCertificateFormula.val s !!(e) u i →
      !(paRangeProofGraph e r).val p d”

noncomputable def uniformRangeProofPreservation (e r : ℕ) :
    ArithmeticSentence :=
  ∀¹* rangeProofPreservationMatrix e r

theorem models_uniformRangeProofPreservation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (e r : ℕ) :
    V↓[ℒₒᵣ] ⊧ uniformRangeProofPreservation e r := by
  rw [models_iff, uniformRangeProofPreservation,
    Semiformula.eval_allClosure]
  intro v
  have hv : v = ![v 0, v 1, v 2, v 3, v 4] := by
    ext j
    fin_cases j <;> rfl
  rw [hv]
  simp only [rangeProofPreservationMatrix,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, Matrix.comp_vecCons'', Matrix.comp₀,
    Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]
  intro h
  have hdEval : Semiformula.Evalb (M := V)
      ![v 3, ORingStructure.numeral r, v 2, v 2]
      rightInstanceCodeGraph.val := by
    simpa [numeral_eq_natCast] using h.1
  have hd := (rightInstanceCodeGraph_iff
    (v 3) (ORingStructure.numeral r) (v 2) (v 2)).mp hdEval
  have hpEval : Semiformula.Evalb (M := V)
      ![v 4, ORingStructure.numeral e, ORingStructure.numeral r,
        v 0, v 1, v 2] rangeProofMapGraph.val := by
    simpa [numeral_eq_natCast] using h.2.1
  have hp := (rangeProofMapGraph_iff
    (v 4) (ORingStructure.numeral e) (ORingStructure.numeral r)
      (v 0) (v 1) (v 2)).mp hpEval
  have hs : Semiformula.Evalb (M := V)
      ![v 0, ORingStructure.numeral e, v 1, v 2]
      (evalnCertificateFormula : ArithmeticSemisentence 4) := by
    simpa [numeral_eq_natCast] using h.2.2
  have hout := rangeProofGraph_rangeProof e r paStageWitness
    primrec_paStageWitness (v 0) (v 1) (v 2) hs
  simpa [paRangeProofGraph, hp, hd] using hout

theorem provable_PA_uniformRangeProofPreservation (e r : ℕ) :
    𝗣𝗔 ⊢ uniformRangeProofPreservation e r :=
  Arithmetic.complete 𝗣𝗔 _ fun (V : Type) _ _ =>
    models_uniformRangeProofPreservation (V := V) e r

end FailureOfComposition.NumericalRangeProofs
