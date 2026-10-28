# Author-side formalization audit

This audit compares the new Boolean-presentation module with version 16 of
*Definability and incompleteness in recursion categories*. It is a scope and
correctness self-audit, not an independent referee or kernel check.

## (A) Kill-shots / hard blockers

For `lem:complete-boolean-presentation`, no local correctness blocker was
confirmed. Its three equivalences are compiled as
`BooleanPresentation.consistent_iff_mono`, `complete_iff_regularEpi`, and
`consistent_complete_iff_isIso`. Their assumptions are a regular extensive
category and an actual regular-epimorphic Boolean presentation. No subobject
equation or preservation-of-unions law is assumed in place of a proof.
Evidence: **structural_argument** and the Lean statements and proof terms.

The full enriched `thm:categorical-essential-incompleteness` still cannot be
claimed. The parameterized input at the actual separator object has not been
constructed from the enriched definability algebra. Failure mode if claimed:
**unproved**; evidence: **absence_in_text**. This remains a major formalization
gap, not a counterexample to the manuscript.

## (B) Major weaknesses

`prop:complete-extensions-and-decisions` remains open. The coproduct of two
terminal objects must be given its internal Boolean algebra structure, its
bound copairing proved a Boolean homomorphism, and characteristic arrows
related to complementary subobjects. The present result that a particular
copairing is an isomorphism does not supply those constructions.

The numerical/PER and arithmetic comparisons remain open, including
`thm:integration-essential-equivalence`, `prop:numerical-boolean-extensions`,
and `cor:arithmetic-representation-incompleteness`. Failure mode if any were
claimed complete: **unproved**; evidence: **absence_in_text**. The imported
typed arithmetic category is not identified with these presentations.

## (C) Minor issues

No new Lean warning or proof-hole marker was found in the new module. Two
pre-existing imported linter warnings remain. The terminology in the current
status and earlier review was corrected to say that an arrow is a regular
epimorphism.

## (D) Cross-section consistency failures

No new identification of restriction idempotents with general predicates, or
of `U` with `S`, is introduced. `BooleanObject.boundCopair` has the manuscript's
order `[bottom, top]`; presentation consistency and completeness use the
upper and lower fibers, and the proofs explicitly commute meet and join.

The consistency proof uses order reflection along the regular presentation
and strictness of initial objects, which follows from extensivity. The
completeness proof instead constructs a pullback square using universal
coproducts, then uses stability and cancellation of regular epimorphisms.
Thus it does not import extra hypotheses from `RiceShapiro/Decisions.lean`.

## (E) Acceptance conditions, non-negotiable

1. The Boolean-presentation lemma and the equivalent bound-copairing conclusion
   must compile, and their transitive axioms must pass the verifier. Met.
2. A full enriched-theorem claim requires constructing the parameterized data
   at `Sep` and the natural comparison through `J`. Not yet met.
3. A decision-equivalence claim requires the Boolean structure and
   characteristic-arrow constructions described above. Not yet met.
4. An arithmetic-interpretation claim requires the numerical/PER and
   provability bridges, distinguishing numeralwise proofs from a proof of a
   single universal sentence. Not yet met.
5. Imported provenance and the pinned source toolchain must be retained. Met.

## (F) Not checked / uncertainty log

Palomar Comparator, NanoDa, and con-ron were not run. No new literature or
novelty claim is made. The manuscript was not edited. The earlier limitation
on retrieving the complete *Mathematical Writing* source remains; no complete
source-based editorial-compliance claim is made.

The strongest confirmed obstacle to the full theorem remains the missing
enriched-data construction. No additional mathematical defect was confirmed.
