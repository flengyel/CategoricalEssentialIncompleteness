import RiceShapiro

/-!
# Axiom check for `RiceShapiro`

Run with:

`lake env lean check_riceshapiro_axioms.lean`

This file is separate from `check_axioms.lean` so that `PCats` and
`RiceShapiro` are checked independently. Both current checks permit only
`propext` and `Quot.sound`; `scripts/syncpcats.sh` enforces this condition.
Future arithmetic-dependent modules will use a separate check file.
Any occurrence of `sorryAx` is an error.
-/

open CategoryTheory

#print axioms ApproximationDatum.extends_comp
#print axioms ApproximationDatum.extends_congr
#print axioms ApproximationDatum.gen_receives
#print axioms ApproximationDatum.gen_mono
#print axioms ApproximationDatum.gen_receives_index
#print axioms ApproximationDatum.StageSelection.rho_apply
#print axioms ApproximationDatum.StageSelection.toWitnessSelection
#print axioms comp_entry
#print axioms DomSemilattice.left_le_join
#print axioms DomSemilattice.right_le_join
#print axioms DomSemilattice.join_le
#print axioms DomSemilattice.invImage_meet
#print axioms DomSemilattice.isQuasicomplement_invImage
#print axioms DomSemilattice.isDense_join_of_isQuasicomplement
#print axioms DomSemilattice.eq_of_agree_on_join_top
#print axioms DomSemilattice.eq_of_agree_on_complement
#print axioms DomSemilattice.Complemented.isQuasicomplement
#print axioms DomSemilattice.complementedInvImage
#print axioms ApproximationDatum.param_total
#print axioms ApproximationDatum.caseComplemented
#print axioms ApproximationDatum.exists_uniformIndex
#print axioms parameterizedRecursion
#print axioms isPartialMono_of_total_test
#print axioms DomSemilattice.Decision.delta_eq
#print axioms existsDecision_of_locallyConnected
#print axioms ApproximationDatum.observationalRiceShapiro
#print axioms ApproximationDatum.categoricalRiceShapiroRepresentation
#print axioms ApproximationDatum.existsExtensionWitness
#print axioms ApproximationDatum.pointwiseRiceShapiro
#print axioms ApproximationDatum.denseUpwardClosure
#print axioms ApproximationDatum.upwardClosure
#print axioms ApproximationDatum.caseJoin_of_dense
#print axioms ApproximationDatum.case_law_zero
#print axioms ApproximationDatum.case_law_entry
#print axioms ApproximationDatum.case_law_eq
#print axioms ApproximationDatum.case_reindex_dom
#print axioms ApproximationDatum.case_reindex_compl
#print axioms ApproximationDatum.case_on_domD
#print axioms ApproximationDatum.case_on_compl
#print axioms ApproximationDatum.generatedSpan
#print axioms ApproximationDatum.mem_gen_iff
#print axioms ApproximationDatum.gen_extensional
#print axioms ExtensionSpan.le_gen
#print axioms ExtensionSpan.gen_le
#print axioms ExtensionSpan.gen_eq
#print axioms CountableExtensionFamily.toExtensionSpan
#print axioms hasExtensionSpanProperty_of_countable
#print axioms gen_eq_of_countableExtensionFamily
#print axioms exists_gen_eq_of_extensional
#print axioms extensional_iff_gen
#print axioms HasRanges.ran_comp_le
#print axioms HasRanges.comp_of_ran_le
#print axioms HasRanges.ran_le_of_receives
