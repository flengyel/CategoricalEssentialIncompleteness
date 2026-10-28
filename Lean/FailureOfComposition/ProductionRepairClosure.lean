/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.ProductionStageClosure
import FailureOfComposition.PrfEqTransportRepair.Soundness

/-!
# Stage bounds required by repair backtranslation

A primitive-recursive translation of repaired equality proofs into the
unchanged production presentation would supply production equality transport.
It would therefore supply the joint stage bound characterized in
`ProductionStageClosure`.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.ProductionRepairClosure

open UniformIndexQuotient ProofSearchMembership PrfEqTransportRepair
open ProductionStageClosure

/-- Backtranslation at equality endpoints suffices; no conversion of other
formula families is used. All five transport arguments vary jointly. -/
theorem repair_backtranslation_implies_transport (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (h : HasPrimitiveRecursiveRepairBacktranslation T hRE) :
    HasPrimitiveRecursivePrfEqTransport T hRE := by
  obtain ⟨back, hpr, hcorrect⟩ := h
  refine ⟨fun z => back (transportPacked z), hpr.comp primrec_transport, ?_⟩
  intro e p y y' d he hp
  exact hcorrect _ _ _ (prfEq_inputs_to_repairTransport T hRE he hp)

/-- An effective repaired-to-production comparison must bound the selected
enumeration of theorems on the transport family. -/
theorem repair_backtranslation_implies_stage_bound (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (h : HasPrimitiveRecursiveRepairBacktranslation T hRE) :
    HasPrimitiveRecursiveStageTransportBound T hRE :=
  (has_transport_iff_stage_bound T hRE).mp
    (repair_backtranslation_implies_transport T hRE h)

theorem no_repair_backtranslation_of_no_stage_bound (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (h : ¬HasPrimitiveRecursiveStageTransportBound T hRE) :
    ¬HasPrimitiveRecursiveRepairBacktranslation T hRE :=
  fun hb => h (repair_backtranslation_implies_stage_bound T hRE hb)

end FailureOfComposition.ProductionRepairClosure
