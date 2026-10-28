# Author-side formalization audit

This audit compares the characteristic-arrow and Boolean-decision construction
with version 16 of *Definability and incompleteness in recursion categories*.
It is a self-audit of scope and correctness, not an independent referee or
kernel check.

## (A) Kill-shots / hard blockers

No correctness blocker was confirmed for the completed target
`prop:complete-extensions-and-decisions`. The proof uses genuine subobjects,
regular epimorphisms, and the constructed internal Boolean algebra on `1 + 1`.
It assumes neither a subobject classifier for arbitrary subobjects nor that
all restriction domains are complemented. Evidence: **structural_argument**
and the compiled Lean statements and proof terms.

The full enriched `thm:categorical-essential-incompleteness` remains incomplete.
The input at the actual separator object has not been extracted from the
enriched definability algebra. Failure mode if full completion were claimed:
**unproved**; evidence: **absence_in_text**. This is a formalization gap, not a
counterexample to the manuscript.

## (B) Major weaknesses

The numerical/PER and arithmetic comparisons remain unproved. The imported
typed arithmetic category has not been identified with the manuscript's
numerical presentation. A completion claim for
`thm:integration-essential-equivalence`, `prop:numerical-boolean-extensions`,
or `cor:arithmetic-representation-incompleteness` would be **unproved**;
evidence: **absence_in_text**. Their construction must preserve the distinction
between numeralwise provability and provability of a single universal sentence.

The arbitrary-arrow clause of `cor:integration-no-boolean-map` is not newly
claimed. The new `no_represented_boolean_decision` proves the case of Boolean
homomorphisms under the explicit external representation hypotheses.

## (C) Minor issues

The three new modules compile without warnings. The two existing imported
linter warnings remain. The source scan found no proof-hole markers or new
axiom declarations, and all 47 transitive axiom audits passed.

## (D) Cross-section consistency failures

No new inconsistency was confirmed. The characteristic arrow sends the
negative subobject to the first inclusion and the positive subobject to the
second inclusion. These are proved to be the lower and upper Boolean bounds.

The Boolean identities are checked over arbitrary generalized elements by
successive restriction to truth-value fibers. Extensivity proves that these
fibers form coproduct decompositions, justifying the equality checks. The
proof does not infer arrow equality merely from equality at global points.

The forward direction reflects complementarity through the injective bounded
lattice map, then uses the inverse of a Boolean isomorphism. The reverse
direction proves that every Boolean homomorphism to `1 + 1` is a split
epimorphism, so its status as a regular epimorphism is derived. The specialized
theorem composes the existing `E`-to-`P` embedding with the subobject comparison;
it does not identify `E` with `P` or assume that distinguished predicates are
in the image of the embedding.

## (E) Acceptance conditions, non-negotiable

1. Construct characteristic arrows and prove their actual fibers. Met.
2. Construct the internal Boolean algebra on `1 + 1` and prove that the bound
   copairing into each Boolean object is a Boolean homomorphism. Met.
3. Prove both directions of the decision equivalence using genuine Boolean
   quotients and the original predicate embedding. Met.
4. A full enriched-theorem claim requires the generalized representative at
   `Sep` and its connection to the manuscript's internal structure. Not met.
5. An arithmetic-interpretation claim requires the numerical/PER and
   provability bridges. Not met.
6. Retain the pinned toolchain, imported provenance, and all previous audits.
   Met. Independent checker status must still be reported separately.

## (F) Not checked / uncertainty log

Palomar Comparator, NanoDa, and con-ron were not run. No literature or novelty
claim is made, and the manuscript was not edited. The previously recorded
limitation on retrieving the complete *Mathematical Writing* source remains;
no complete source-based editorial-compliance claim is made.

The strongest confirmed obstacle to the full categorical theorem remains the
missing enriched input construction. No additional mathematical defect was
confirmed in this checkpoint.
