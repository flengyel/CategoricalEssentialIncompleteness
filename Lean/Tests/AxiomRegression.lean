/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import RiceShapiro

/-!
# Axiom envelope regression test

The three headline results, with their axiom dependencies printed. The purpose
is to detect accidental introduction of `sorryAx`, of `Classical.choice`, or of
any axiom outside the permitted envelope.

`#print axioms` reports rather than judges: it prints whatever the dependency
set has become and elaboration still succeeds. The judgement is made by
`scripts/syncpcats.sh`, which fails the run when this file's output mentions
`sorryAx` or names an axiom outside `{propext, Quot.sound}`. That script also
refuses a vacuous pass if the `#print axioms` output disappears entirely, so
deleting a line here fails the run rather than silently narrowing coverage.

These three declarations are also covered by `check_riceshapiro_axioms.lean`,
which prints the axioms of the whole `RiceShapiro` surface. The duplication is
deliberate: this file is the short list that must never regress, and it is
grouped with the signature guards it belongs to.
-/

@[expose] public section

open CategoryTheory

#print axioms existsDecision_of_locallyConnected
#print axioms ApproximationDatum.categoricalRiceShapiroRepresentation
#print axioms ApproximationDatum.existsExtensionWitness
