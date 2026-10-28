# Author-side formalization audit

This audit compares the internal separator construction with version 16 of
*Definability and incompleteness in recursion categories*. It is a self-audit
of scope and correctness, not an independent referee or kernel check.

## (A) Kill-shots / hard blockers

No correctness blocker was confirmed for the factorization proved from the
explicit internal total-arrow and predicate structures. The construction uses
the actual complementary-pair pullback, representation pullback, separator
equalizer, and bound equalizer in an arbitrary finitely complete base.
Evidence: **structural_argument** and compiled Lean statements and proof terms.

The full enriched theorem is not claimed. `InternalHom` and `InternalPredicates`
have not yet been constructed from the manuscript's enriched restriction
hom-objects. In particular, the lattice sort `E_X` has not been identified
with the fixed-point equalizer of restriction, nor the hom-object with the
totality pullback. A claim to have completed that comparison would be
**unproved**; evidence: **absence_in_text**. This is a formalization gap, not a
counterexample to the manuscript.

## (B) Major weaknesses

The global-element comparison with the ordinary restriction category and
external `DiagonalData`, and its connection to `J` and the natural subobject
identification, remain open. The existing external restriction-domain
construction is not silently used as an internal comparison.

The numerical/PER and arithmetic comparisons remain unproved. The imported
typed arithmetic category has not been identified with the numerical
presentation. A completion claim for `thm:integration-essential-equivalence`,
`prop:numerical-boolean-extensions`, or
`cor:arithmetic-representation-incompleteness` would be **unproved**;
evidence: **absence_in_text**. Numeralwise provability must remain distinct
from provability of a single universally quantified sentence.

## (C) Minor issues

All four new modules compile without warnings. The two existing imported
linter warnings remain. The scan of all fourteen project Lean files found
no proof-hole markers or new axiom declarations. All 62 axiom audits passed,
retaining the previous 47. The audit initially detected a stale generated
entry-point artifact; after rebuilding that artifact, the full verifier passed.
No source or dependency modification was needed to resolve that artifact issue.

## (D) Cross-section consistency failures

No new inconsistency was confirmed. Internal operations are actual morphisms
in the base. Their category, product, and predicate-action equations hold at
all parameter objects; no assumption that global points detect equality is
used. Monicity of the internal embedding gives injectivity at every parameter.

The complementary-pair object is the pullback of the meet/join arrow along
the pair of bounds. Its universal projections are proved complementary, and
a complementary pair at any parameter gives a lift. The representation
section supplies `rho` and both representation equations. Conversely, those
universal equations construct a section. Existence of a separator, equality
of bounds, and the desired factorization are not assumed as structural fields.

The actual separator equalizer gives complementary morphisms `a,b : Sep → E_S`
and the separator inequalities in `P_S`. Pulling the reversed pair back along
`delta` constructs `gamma : Sep → C_U`. The representative is
`gamma >> rho`, which varies over `Sep`. The product identities, naturality
of the embedding, and distributivity prove equality of complementary
pullbacks. The resulting equality of the two bounds as maps out of `Sep`
gives the required equalizer lift.

`U` and `S`, and the lattice sorts `E` and `P`, remain separate. No global
complementation and no representation of the distinguished predicates through
`j_S` is assumed. The strict-initial consequence uses the constructed arrow
to the initial bound locus, not the absence of global separators.

## (E) Acceptance conditions, non-negotiable

1. Construct the actual complementary-pair object and its generalized lifts.
   Met.
2. Derive generalized representatives from the actual representation section.
   Met for the explicit internal total-arrow and predicate structure.
3. Construct the actual separator and prove its factorization and both stated
   consequences over the specified base. Met for that structure.
4. Derive this internal structure from the enriched restriction hom-objects
   and complete the global comparison with the functor `J`. Not met.
5. Establish the numerical/PER and provability comparisons before claiming
   arithmetic essential incompleteness. Not met.
6. Retain the pinned toolchain, imported provenance, and every previous
   audit. Met. Independent checker status remains separate.

## (F) Not checked / uncertainty log

Palomar Comparator, NanoDa, and con-ron were not run. No literature or novelty
claim is made, and the manuscript was not edited. The previously recorded
limitation on retrieving the complete *Mathematical Writing* source remains;
no complete source-based editorial-compliance claim is made.

The next unresolved construction is the internal total-arrow and restriction-
idempotent reduct from enriched restriction hom-objects. No additional
mathematical defect was confirmed in this checkpoint.
