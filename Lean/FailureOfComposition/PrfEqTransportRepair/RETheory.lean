/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.PrfEqTransportRepair.Structural

/-!
# The transport repair at a selected r.e. theory

This file specializes the structural checker to the stage witness already
selected by the production proof bridge.  It gives the repaired `PrfEq`
endpoint an exact Sigma-one formula and exposes the PA proof that transport
preserves that endpoint with all numerical data internally quantified.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Structural Arith.Feferman.Specialization

namespace FailureOfComposition.PrfEqTransportRepair

open NumericalProofBridge ProofSearch UniformIndexQuotient

noncomputable def reTheoryTransportRepairProofGraph
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝚺₁.Semisentence 2 :=
  transportRepairProofGraph (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

theorem reTheoryTransportRepairProofGraph_nat_iff
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (p a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, a]
        (reTheoryTransportRepairProofGraph T hRE).val ↔
      Proof_T (reTheoryTransportRepairPresentation T hRE) p a := by
  exact transportRepairProofGraph_nat_iff
    (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE) p a

/-- The exact arithmetic endpoint of the repaired checker.  Its variable order
is `(p,q,r)`, matching `ProofSearchMembership.prfEqFormula`. -/
noncomputable def repairPrfEqFormula
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝚺₁.Semisentence 3 := .mkSigma
  “p q r. ∃ a, !equalityCodeGraph a q r ∧
    !(reTheoryTransportRepairProofGraph T hRE) p a”

@[simp] theorem repairPrfEqFormula_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (p q r : M) :
    Semiformula.Evalb (M := M) ![p, q, r]
        (repairPrfEqFormula T hRE).val ↔
      Semiformula.Evalb (M := M)
        ![p, equalityCodeValue q r]
        (reTheoryTransportRepairProofGraph T hRE).val := by
  simp [repairPrfEqFormula, equalityCodeGraph_iff]

@[simp] theorem repairPrfEqFormula_nat_iff
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (p q r : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, q, r]
        (repairPrfEqFormula T hRE).val ↔
      RepairPrfEq T hRE p q r := by
  rw [repairPrfEqFormula_eval, equalityCodeValue_nat,
    reTheoryTransportRepairProofGraph_nat_iff]
  rfl

noncomputable def reTheoryUniformTransportPreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    ArithmeticSentence :=
  uniformTransportPreservation (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

/-- PA proves preservation by the repaired constructor with both input proof
codes, all three program indices, all three equality-formula codes, and the
result proof code quantified inside the sentence. -/
theorem provable_PA_reTheoryUniformTransportPreservation
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝗣𝗔 ⊢ reTheoryUniformTransportPreservation T hRE :=
  provable_PA_uniformTransportPreservation
    (reTheoryStageWitness T hRE)
    (primrec_reTheoryStageWitness T hRE)

end FailureOfComposition.PrfEqTransportRepair
