# Hostile-referee review of the v28 revision

Scope: the v27-to-v28 mathematical changes recorded in `tmp/move28/main.diff`, read in their full current passages in *Logical consequence and essential incompleteness in recursion categories*, version 28. This is an author-side audit, not an independent journal referee report. The current-source archive is extracted in `tmp/review29/baseline/local_connectedness`; source anchors below use `output/manuscript/local_connectedness`.

## (A) Kill-shots / hard blockers

None confirmed in the reviewed revision. In particular, no missing local-connectedness or weak-choice hypothesis was found in the replacement argument. Corollary 3.3 constructs the required target morphism from an explicitly total source morphism; it does not invoke the removed section-existence proposition.

Typed check of the replacement proof: `ell_c:U -> U+U`; `epsilon_i:U+U ~> U+U`; `[c,c']:U+U ~> U`; `chi:FU+FU -> F(U+U)`; and `s_c=chi^{-1}F(ell_c):FU -> FU+FU`. The two summand-restriction identities follow by composition with `c,c'` and range agreement. Taking restrictions gives the two inverse-image equations. A range functor sends a complementary source separator to a complementary target separator. Corollary 3.2 then excludes the constructed lift. Every displayed composition in this replacement is well typed.

## (B) Major weaknesses

None confirmed in the reviewed changes.

## (C) Minor issues

### C1. The introduction calls the abstract categorical conclusion recursive inseparability

- Anchor: `sections/01-introduction.tex:3–6`, “establishes recursive inseparability in a recursion category”.
- Claim as written: Corollary 3.3 establishes recursive inseparability in an arbitrary recursion category satisfying its hypotheses.
- Failure mode: `inconsistent_use`.
- Why it fails as written: Section 2 defines inseparability of restriction idempotents by exclusion of a complementary pair. Corollary 3.3 proves precisely that categorical property; it does not assert the existence of numerical sets or an interpretation as partial recursive functions for an arbitrary source category. The numerical applications subsequently supply that interpretation.
- Evidence: `structural_argument`; compare the definition at `sections/02-categorical-preliminaries.tex:43–44` and conclusion at `sections/03-sections-and-inseparability.tex:114–115`.
- Downstream impact: imprecise introductory description, with no defect in the corollary or its applications.
- Severity: minor. Repairability: local wording.
- Recommended replacement: “Corollary~\\ref{cor:source-conditionals} establishes inseparability of restriction idempotents in a recursion category using a range functor and specified total morphisms …”.

### C2. Appendix C still verifies target properties that the relocated criterion no longer uses

- Anchor: `appendices/c-section-lifting.tex:124–128`, “Its target … is split and locally connected” and “giving weak choice”.
- Claim as written: the proof additionally verifies splitness, local connectedness, and weak choice for `Pfn`.
- Failure mode: `unused_hypothesis` as an exposition issue, not an omitted or false theorem hypothesis.
- Why it fails as written: Proposition C.1 now states the properties relevant to Theorem 3.1/Corollary 3.2. Its statement no longer includes these three properties, and the remainder of Appendix C does not invoke them. The paragraph is a remnant of the criterion that moved to the separate note. The concrete partial-inverse argument for the particular `s_A` is supplied separately at lines 170–186.
- Evidence: `absence_in_text` plus direct inspection of the complete Appendix C proof; the relevant surviving target facts are the total inverse-image union law and `F(1_N) != 0`.
- Downstream impact: unnecessary preparation obscures which assumptions the counterexample tests.
- Severity: minor. Repairability: delete only the unused assertions and keep the inverse-image statement.
- Recommended replacement for lines 122–128: “The functor $F$ is faithful and preserves restrictions, zeros, ranges, binary restriction products, and coproducts. It also reflects zero morphisms. Total inverse images in $\\Pfn$ preserve unions, and $F(1_{\\N})\\ne0$.”

## (D) Cross-section consistency failures

C1 is the only confirmed terminology mismatch in the changed text.

The changed application dependencies are consistent:

- Model interpretation: Lemma 6.2 supplies the source conditional; Proposition 6.1 supplies the range functor; nonempty models give the nonzero identity; total set-theoretic inverse images preserve unions.
- Miller application: the parallel domain searches are programs for source morphisms of `E_a`, rather than programs chosen for a single representation. Complementarity and the common source domains imply that the output tag and value are independent of the representation. The proof of the Turing morphism, which still needs the earlier unanimity lemma, is not replaced by this simpler conditional construction.
- Three-point application: the inverse of `q=[m,m']` is computed componentwise, and its naturality is explicitly stated. Consequently the copairing defining `ell_c` is a total natural transformation. Fullness puts it in the recursion subcategory. The target retains all required restriction structure and its inverse-image join law.
- Endpoint application: `K_2` is full on the stated objects, so total recursive conditionals belong to it. The reference to the earlier numerical construction supplies the same opposite-tag convention. Writing the two equations explicitly here would be optional clarification rather than repair of a missing inference.
- Appendix C: the counterexample still has a complementary target pair and target conditional, while the conditional has no source preimage. Thus it does test omission of the lift in the retained theorem.
- Appendix D: the single source conditional exists before passing to model coordinates. Coordinatewise images satisfy the same equations; no independent choice of source indices is asserted.

No new undefined category-theoretic construction or invented mathematical noun was confirmed in these changed passages. “Complementary conditionals” has the explicit local meaning fixed by the displayed pair of equations; it does not conceal an additional structure or hypothesis.

## (E) Acceptance conditions, non-negotiable

1. Replace the introductory description identified in C1 by the categorical conclusion actually proved. Endpoint: the opening paragraph says inseparability of restriction idempotents; numerical recursive inseparability remains in the applications. Failure leaves a local exposition defect, not a reason to reject the theorem.
2. Remove the unused target-property verification identified in C2, preserving the concrete counterexample and the inverse-image union law. Endpoint: Appendix C proves only the target properties it states or later uses. Failure leaves unnecessary exposition, not a mathematical rejection condition.

No theorem, construction, or application must be dropped on the evidence of this review.

## (F) Not checked / uncertainty log

The audit covers the v28 changes and the contextual definitions and proofs needed to type-check them. It is not a new full review of the unchanged internal syntax, proof-system initiality, arithmetization, Miller compactness argument, or the construction of the three-point Turing morphism. No Lean kernel checking, compilation, or visual inspection was performed by this reviewer. No new literature or novelty claim was introduced in the reviewed changes; antecedent and citation accuracy were not independently rechecked.

Strongest confirmed blocker: none. Strongest confirmed defect: C1, an introductory description broader than the categorical conclusion it cites. Strongest suspected unconfirmed blocker: none identified within this scope. Most important unchecked material: the unchanged realization and Turing-morphism constructions on which the applications depend. The scope-local findings do not depend on unavailable material. Final recommendation: **unknown** for the whole manuscript, because that manuscript was not reread in full; the reviewed revision supplies no confirmed mathematical ground for rejection.
