module

public import Arith

/-!
# Axiom check for `Arith`

Run with:

`lake env lean check_arith_axioms.lean`

`scripts/syncpcats.sh` fails the run when this file's output names an axiom
outside `{propext, Classical.choice, Quot.sound}`, or names `sorryAx`. That is
the same envelope enforced on `Metamath`, and wider than the
`{propext, Quot.sound}` enforced on `PCats` and on `RiceShapiro`; those checks
are separate files over separate roots and are unchanged.

## Coverage

The check audits all eight public declarations of
`Arith.Feferman.ProofFormula`, the structural proof graph and its PA closure
milestones, fixed-formula numeral substitution, and the numerical
specialization milestones used by
`FailureOfComposition`. The structural modules contain many supporting graph
lemmas; the selected declarations below are the public acceptance boundary for
the new proof-code transformations.

`Arith.Feferman.ProofFormula` has two private declarations,
`primrecPred_proofTPacked` and `computablePred_proofTPacked`. Private
declarations are not public and are not listed.

No external Foundation or Mathlib probe appears in this file. The measured
dependencies of the pinned declarations these results are built from are
recorded in `check_metamath_axioms.lean` for the `Primrec` layer and in
`Audit/task-b0b-r0-probe-output.txt` for the Foundation layer.

## Where `Classical.choice` appears

Every audited declaration lists `Classical.choice`. Foundation's
representation results and Mathlib's `Primrec` infrastructure both depend on
pinned declarations that list it. `#print axioms` reports the axioms of a
declaration's type together with those of its proof term and does not
distinguish the two, so nothing here should be read as a claim about which of
the two introduces a given axiom.

`Metamath.Feferman.Proof_T` itself remains `[propext, Quot.sound]`; that record
is enforced by `check_metamath_axioms.lean`, not by this file.
-/

@[expose] public section

open Arith.Feferman

#print axioms proofTPacked
#print axioms proofTPacked_pair
#print axioms rePred_proofTPacked
#print axioms delta1_proofTPacked
#print axioms proofTFormula
#print axioms proofTFormula_sigma_one
#print axioms proofTFormula_nat_iff
#print axioms proofTFormula_weak_representation

#print axioms Arith.Feferman.Structural.listDecodeGraph_iff_listEncodeGraph
#print axioms Arith.Feferman.Structural.proofGraph_nat_iff
#print axioms Arith.Feferman.Structural.proofGraphWithLogicalAxiom_nat_iff
#print axioms Arith.Feferman.Structural.provable_PA_uniformMPClosure

#print axioms Arith.FixedFormulaNumeralSubstitution.primrec_arithmeticNumeral
#print axioms Arith.FixedFormulaNumeralSubstitution.primrec₂_arithmeticSemisentenceNumeralSubst
#print axioms Arith.FixedFormulaNumeralSubstitution.primrec_arithmeticSemisentenceNumeralSubst₃
#print axioms Arith.FixedFormulaNumeralSubstitution.primrec₂_firstNumeralUnderTwoBinders
#print axioms Arith.FixedFormulaNumeralSubstitution.primrec₂_secondNumeralUnderStageAndTwoBinders

#print axioms Arith.Feferman.Specialization.primrec_specialize
#print axioms Arith.Feferman.Specialization.primrec_transferForward
#print axioms Arith.Feferman.Specialization.primrec_transferReverse
#print axioms Arith.Feferman.Specialization.proof_T_specialize
#print axioms Arith.Feferman.Specialization.proof_T_transferForward
#print axioms Arith.Feferman.Specialization.proof_T_transferReverse
#print axioms Arith.Feferman.Specialization.specializationProofGraph_nat_iff
#print axioms Arith.Feferman.Specialization.provable_PA_uniformSpecializationPreservation
#print axioms Arith.Feferman.Specialization.provable_PA_uniformForwardTransferPreservation
#print axioms Arith.Feferman.Specialization.provable_PA_uniformReverseTransferPreservation
