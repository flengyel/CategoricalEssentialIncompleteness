# Finite-support constructions for Lemma 8.9

Four producer/Checks pairs construct prerequisites for Lemma 8.9. They do
not complete its internal-consistency or essential-incompleteness conclusions.
The current count remains **70 of 77 numbered results proved**, with seven open.
Theorem 5.3 remains complete. The mathematical statements of v58 and v59
are identical.

## Constructions

`V46DerivationInternalInduction.model_rule_induction` proves rule induction
for Pi-one invariants with model parameters on the actual coded derivation
carrier, in every model of an arithmetic theory extending PA. The existing
typed constructor decomposition and decrease of child node counts supply
the successor step. PA induction proves the invariant for every internal
node count. There is no standard-model or external well-foundedness premise,
and interpretation is not assumed to preserve initial algebras.

`V46DerivationFiniteSupport` constructs an inference algebra with carrier
`Fm times List(X)` over `Fm`. Its fold retains each original conclusion and
collects prescribed lists at nullary leaves, retains a unary child's list,
and concatenates both binary lists. The constructor equations use the original
typed premise pullbacks. `nullaryLabels` lists the original nullary rule
instances. The arithmetic statement check instantiates the fold with
`SyntacticDerivation.derivationAlgebra` and its constructed initiality. The
positive-leaf assignment for the printed signed theory is not supplied by
this generic fold and remains to be constructed.

`V46ArithmeticFiniteLookup` defines a concrete canonical-vector recursion:
nil returns zero; a cons step returns one when the searched label equals the
head, and otherwise retains the tail's result. Its Sigma-one recursive graph
is proved equivalent in PA to the Delta-one membership specification. The
proof applies at arbitrary internal vector lengths in every PA model. The
standard function is proved primitive recursive using the existing canonical
vector comparison. This is a model-level graph comparison with an actual
recursive definition, not an inference about nonstandard models from
standard extensional equality.

`V46ArithmeticSignedFiniteSupport` proves support concatenation equations
and specializes finite lookup to the actual diagonal predicates alpha and
beta. Every positive member of either support is assigned one in their
concatenation. PA proves that each beta-label is assigned zero whenever all
entries in the support satisfy alpha. The existing PA-provable disjointness
of the diagonal predicates supplies this last conclusion.

These numerical values still require their comparison with the categorical
Boolean morphisms when the valuation is assembled. Truth remains the second
coproduct injection and quantification the second projection. No general
initiality binder, consistency hypothesis or extension quantifier is changed.

## Verification

All eight producer and Checks files pass strict elaboration with warnings
treated as errors. Their thirteen printed principal transitive axiom reports
use only `propext`, `Quot.sound` and `Classical.choice`. The
[incremental record](V59_FINITE_SUPPORT_INCREMENTAL_VERIFICATION_2026-11-14.json)
lists the exact commands and source hashes. The new modules are imported
through the production entry, both statement entries and the complete current
axiom audit. The full locked verification execution is recorded separately;
the incremental record alone does not claim a full replay.

The parser's six tests and the v59 manuscript gate pass. The article changes
only bibliography typesetting and version metadata; the reviewed v58 artifacts
are retained. The [Google assessment](reviews/GOOGLE_V58_2026-11-14/assessment.md)
records the review's four concrete items independently of the Lean work.

## Next construction

Instantiate the leaf assignment with the actual positive signed-axiom labels,
prove support coverage and the concrete extraction properties, then construct
the Boolean valuation in the support-parameter slice. Prove the truth invariant
for both derivations by internal induction, including negative leaves, equality,
admissible substitution, the seven schemes, modus ponens and generalization.
Identify the resulting PA consistency sentence with the printed generated
sentence subobject. Apply the existing signed-theory incompleteness criterion
only after that construction. Keep Lemma 8.9 and Corollary 8.10 open until
their complete printed statements have proved checks.
