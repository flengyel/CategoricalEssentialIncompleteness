# Version 45 introduction and attribution: author-side hostile review

Scope: all changed TeX prose compared directly with the frozen version 44 sources, the two organization/attribution reports, and the relevant logical comparison and source-inseparability statements. The comparison found changes in the introduction, six body/appendix files, and version metadata. No theorem, definition, displayed equation, or proof has been changed by this revision. This review does not reopen all body proofs or certify originality.

## (A) Kill-shots / hard blockers

None established. The shorter introduction retains the Di Paola–Heller objective and methodological criterion, the internal deductive construction, a typed range functor with its source and target categories, the soundness/negation compatibility condition, and the reduction/lifting conditions for the semantic comparison. The arithmetic model is introduced before its functor, and the three applications retain their distinct effective extension classes.

## (B) Major weaknesses

Anchor: the introduction paragraph beginning “The first criterion uses a range functor”, specifically “The second criterion starts with an inseparable pair and applies it to the theorem and refutation restriction idempotents of every consistent extension represented in the same category”. Failure mode: unproved generality as written. Evidence: derivation from Corollary 4.3. An inseparable pair cannot be applied to arbitrary represented theories merely because they inhabit the same category. The corollary requires a total reduction of the fixed pair to the theorem/refutation idempotents of a base theory; monotonicity then preserves that reduction for extensions. The shortened sentence suppresses this load-bearing hypothesis. Severity: local and repairable. Recommended repair: “The second criterion starts with an inseparable pair reduced by a total morphism to the theorem and refutation restriction idempotents of a base theory, and yields incompleteness for every consistent represented extension of that theory.” This single qualification restores the dependency without returning the technical tutorial to the introduction.

## (C) Minor issues

No additional correction is required by the inspected changes. The compact account of the internal theory is explicitly scoped to the realizations studied here. It therefore does not assert that every recursion category's completion automatically has the syntax, regular images, or partial inverses required by the body construction. The restriction terminal qualification in the Cockett comparison and the derived status of Löb in Ramesh remain explicit.

## (D) Cross-section consistency failures

Apart from (B), none established in the changed prose. The exact v44-to-v45 diff shows that technical definitions and arguments removed from the introduction remain in their existing body locations. The source credits are attached to the borrowed construction or definition:

- Section 2 credits the restriction-category definition to Cockett–Lack §2.1.1, which is the source's definition section.
- Section 5 credits Montagna and Di Paola–Montagna for the syntactic recursion categories, while retaining the paper's product/coproduct presentation.
- Section 8 credits Miller's sequence and the following-paragraph index property, with Bauer–Hanson's binary-representation formulation; it does not attribute the new recursion category or logical application to those sources.
- Section 6.4 credits Łoś's theorem through Keisler before the ultrapower comparison; it does not assign the new comparison lemma to Keisler.
- Section 9 credits Curry's cosheaf definition and Cockett–Lack's partial-map construction separately. Cockett–Lack §3 explicitly constructs the partial-map category and proves its restriction structure. No claim that Curry supplies the new three-point recursion category is made.
- Appendix A moves the existing list-recursion citations and uniqueness-gap footnote to the opening, preserving the restriction of the citation to the unaffected results. Its Gabbay–Pitts comparison remains a comparison of the structural-recursion method, not attribution of the entire present substitution construction.

The target of the comparison is still a split restriction category, without a target recursion-category or target-inseparability assumption. The arithmetic statement retains the distinction between the model interpreting program graphs and a model interpreting the decoded formulas. The Miller statement retains one oracle program working across all binary representations. The propositional statement retains same-language, computably enumerable axioms.

## (E) Acceptance conditions, non-negotiable

Restore the total-reduction-to-a-base-theory qualification in (B). Endpoint: the shortened second-criterion sentence states the actual hypothesis that connects the fixed inseparable pair with the generated theory and its represented extensions. Verify references and the rendered revised pages before delivery. No other local mathematical repair is required by this review.

## (F) Not checked / uncertainty log

The body proofs and all bibliography entries were not re-audited. Source placements were checked against the existing source record and, for the new precise restriction/partial-map placements, the cached primary text. Most important thing not checked: full mathematical correctness of the application proofs. Strongest confirmed blocker: the missing total-reduction condition in (B). Strongest suspected unconfirmed blocker: none established by this diff. No unavailable material affects the local recommendation. Final recommendation: unknown for acceptance of the entire paper; the indicated single local qualification is required before this prose revision is delivered.

## Resolution in the final version 45 source

Reinspection confirms that the second criterion now explicitly uses a total morphism reducing a fixed inseparable pair to the theorem and refutation restriction idempotents of a base theory, and applies the same reduction to every consistent represented extension of that theory. This resolves (B). No remaining defect is established in the changed prose or attribution placements within this review's scope.

The further organization change was also inspected: the roadmap now precedes the Related work heading, and the subsection itself contains only the literature comparisons. The corrected criterion paragraph remains in the exact current source. No additional finding arises from this move.
