## (A) Kill-shots / hard blockers

Author-side AI-assisted review of the new formalization batch. The reviewed
manuscript is *Logical consequence and essential incompleteness in recursion
categories*, v46, publication commit
`558a20eed4c62d59eada05f5500cf233671078e9`, with entry point
`manuscript/latex/main.tex`. PDF page numbers below are one-based PDF pages.
This review applies the HostileRefereeGPT plugin's evidence-bound review
workflow. It is a source and correspondence review, not an independent kernel
replay or a novelty assessment.

No false theorem, ill-typed mathematical statement, or hidden strengthening was
found in the four new Section 3 statements after inspection of their source
proofs and explicit statement checks. The following is a hard blocker to a
claim that **all of v46** has been formalized; it is not a counterexample to
the manuscript.

**A1. The concrete categorical realizations remain unproved.**
Anchor: PDF p.16, Proposition 5.5, “for every object P,” and PDF p.42,
Lemma 8.1, “one oracle program.” The first statement quantifies over arbitrary
coefficient objects and every parameter slice; the second requires the same
domain and values for every binary representation of the fixed sequence.
Failure mode: **unproved**, if either is claimed completed by the old syntax
recursors or by computation relative to a chosen oracle.
Evidence: **absence_in_text / structural_argument**. The new categorical syntax/list interfaces correctly record initiality
in all parameter slices as the assumptions of Definition A.1; they do not
construct such initiality in the promised examples. Existing global recursors
have no arbitrary slice-algebra universal property; the v46 inventory records
no representation-independent Miller category or its concrete inference
algebra. A conditional image theorem for an arbitrary endofunctor does not
construct either application. Downstream impact: the full Section 5 syntax
realization, the indexed arithmetic family, and all of Section 8 remain
application obligations. Severity: **major** for formalization completeness;
repairable by the constructions named in the correspondence table. No claim
that these mathematical statements are false is made.

## (B) Major weaknesses

**B1. Generic named-variable substitution is still unconstructed.**
Anchor: PDF p.57, Proposition A.3, “Parameterized initiality uniquely
determines morphisms.” The new categorical syntax and list modules specify
the polynomial, initiality in all parameter slices, and unique folds at
arbitrary coefficient objects. These are legitimate abstract assumptions of
Definition A.1. Failure mode: **unproved** for the further construction of
option-valued substitution and complemented admissibility. Evidence:
**absence_in_text / structural_argument**. The occurrence-list fold and
sentence pullback are implemented. Substitution needs its specific algebra;
the retained-original/result algebra and its quantifier branch must actually
be constructed, using occurrence lists and the free-for test, before its
success fiber gives the printed admissibility subobject. The new generic
fold alone is insufficient. Downstream impact: Appendix A.3/A.6 and the
concrete first-order realizations. Severity: **major** for full correspondence;
repairable by the named-variable operations, algebra and pullback proofs.

**B2. Arithmetic requires the fixed syntactic semantic chain.**
Anchor: PDF p.28, Lemma 7.2, “A partial proof-search lift,” and PDF p.29,
Theorem 7.3, “Apply Theorem 4.2.” Failure mode: **unproved** for the required
concrete application, not for the old numerical incompleteness consequence.
Evidence: **structural_argument / absence_in_text**. A total conditional on
complementary predicates does not supply the partial search on an arbitrary
consistent theorem/refutation pair. The standard-code validity factorization,
ultrapower comparison, nonstandard diagonal bounds, and partial proof-search
graph equation must all be represented in the fixed source `S_PA` before the
new abstract comparison applies. Downstream impact: the advertised internal
and ultrapower incompleteness proof and uniform family. Severity: **major**;
repairable by Section 6/7 constructions, recorded separately from existing
numerical consequences.

**B3. Endpoint theorem sets and arbitrary c.e. axiom sets require distinct
realizations.** Anchor: PDF p.53, Corollary 9.6, “computably enumerable axiom
set.” The new endpoint results quantify over actual c.e. theorem-code sets
or their restriction idempotents; they do not assume a compatible family for
an individual endpoint extension. Failure mode: **unproved** for the remaining
axiom-to-theorem construction if full Corollary 9.6 is claimed.
Evidence: **derivation**. `endpoint_ce_extension_incomplete` constructs
`EnumerableCarriers.relativeIdem T`, proves its support equals T, transfers
consistency to restriction disjointness, and produces a code outside T and its
negation inverse image. To instantiate this from an arbitrary c.e. axiom set,
the finite-proof closure must be constructed and shown c.e., extending the
base theorem set. The existing initiality of the propositional syntax algebra
does not establish initiality of the typed inference algebra in the slice
(Proposition 9.3). Severity: **major** for the full realization; the proved
theorem-set result remains valid.

## (C) Minor issues

No confirmed mathematical wording or typing defect requires a manuscript
change. The v46 manuscript sources and version remain unchanged by this batch.

The status table uses the actual `main.tex` input order: there are 62 numbered
results and three numbered definitions. In particular, A.4 is a definition,
A.5 is the least-image theorem, and the source file
`04-miller-sequences.tex` is Section 8. The source table and statement checks use these actual v46 numbers.

## (D) Cross-section consistency failures

No confirmed inconsistency was found in the changed abstract proof chain.
The following checks establish the correspondence and its limits.

1. **Theorem 3.1:** PDF p.5, “disjoint restriction idempotents.”
   `comparison_zero_inverse_images` takes arbitrary disjoint `P,N : Idem (F U)`;
   `s` and `ℓ` are arbitrary morphisms and carry no totality premises. The proof
   first obtains total `g` and `g ≫ h = g ≫ ℓ` from source Turing universality,
   applies `F`, and composes with the inverse coproduct comparison. It proves
   the reversed inverse-image equalities, mutual inequalities, and zero from
   disjointness. No product preservation, splitting, local connectedness,
   weak choice or global join-inverse premise is introduced.

2. **Theorem 3.1 noncoverage and Corollary 3.2:** PDF pp.5–6,
   “preserves the join P ∨ N.” `comparison_noncoverage` uses the same explicit
   witness `g`, its totality, the two zero equations, nonzero mapped identity,
   and that one join equation. Corollary 3.2 obtains this equation from
   `TotalJoinInverse A`; arbitrary-partial join preservation is unnecessary.
   In the trivial zero-identity case the zero-inverse-image theorem still
   applies and the separately stated nontriviality premise correctly prevents
   the noncoverage conclusion.

3. **Corollary 3.3:** PDF p.6, “agreement law for ranges.” The proof of
   `switch_fibers`, used by the new source-inseparability theorem, invokes
   `complementary_hom_ext`, which uses `Ranges.agreement` on `[c,c′]` and its
   top range. Its elaborated dependencies do not require a section-selection
   or local-connectedness theorem. Mapping the total source conditional and
   composing with `χ.inv` gives exactly the required target fibers.

4. **Proposition 3.4:** PDF p.7, “join in the restriction order.”
   `PairComplementary` expresses disjointness and least-upper-bound coverage
   directly. `DisjointArrowJoins` supplies the join of the two branches; the
   upper-bound equations give the agreement equations, and both domains lie
   below the join's restriction, forcing totality. The result works in an
   arbitrary restriction category with zeros and restriction coproducts.

5. **Section 4 helpers:** PDF pp.8–9, Proposition 4.1/Theorem 4.2.
   `logical_comparison_target` has an arbitrary target object S, a total
   `θ : F U ⟶ S`, and semantic consistency; it applies Theorem 3.1 and total
   inverse-image joins along `F g ≫ θ`. Its unused need for total negation is
   omitted, yielding a valid more general helper. Source noncoverage is a
   separate proved transport through a range functor. The final `logical_comparison` uses the constructed chosen-splitting
   extension and the natural inclusion comparison to obtain the two source
   composite zero equations and source noncoverage. Its explicit statement
   check includes a split target and total negation. The manuscript assumes
   the sentence-theory idempotent; its concrete realization is tracked in
   the application rows. Proposition 4.1 still requires the generic
   partial-map realization for the validity-subobject factorization.

6. **Lemma A.7:** PDF p.60, “If m has a partial inverse r.” The new
   `LC.V46.range_regularImage` retains both partial-inverse equations on the
   specific image inclusion. It uses a splitting of the range and the regular
   epi/mono lifting square to show that the image inclusion is received by
   the range; leastness gives the converse inequality. It does not assume
   that every total monomorphism has a partial inverse.

7. **Endpoint applications:** PDF pp.52–53, Theorem 9.5/Corollary 9.6.
   The new `endpoint_essential_incompleteness` uses the actual endpoint Turing
   pair and the proved transferred atomic inclusions, followed by the exact
   domain-incompleteness theorem. `endpoint_complete_iff` compares categorical
   noncoverage with failure of theorem/refutation coverage on the full
   numerical carrier. This repairs the narrower old conclusion that only
   asserted noncoverage of the whole compatible family. The inference-algebra
   realization and general c.e.-axiom instance remain distinct obligations.


8. **Corollary B.9:** PDF p.67, “Every idempotent in A splits.”
   `idempotent_splits_through_range` proves this for an arbitrary split
   restriction category with range agreement. If `a = range f`, the agreement
   law applied to `f ≫ f = f ≫ 1` gives `a ≫ f = a`. For a chosen split
   `m ≫ r = 1`, `r ≫ m = a`, set `s = f ≫ r`; then `m ≫ s = 1` and
   `s ≫ m = f`. The inclusion on Karoubi envelopes is full and faithful;
   dominance gives essential surjectivity for arbitrary target idempotents.
   Composing with the ambient idempotent-completion equivalence gives
   `Karoubi Rec ≌ Object`. A separate foundations agent inspected these
   equations and found no defect or additional hidden hypothesis. The added
   natural source comparison and explicit statement check have compiled. The
   unnumbered restriction operation on the arbitrary-idempotent Karoubi
   envelope and preservation by the equivalence are separately pending; the
   numbered result asserts the ordinary equivalence proved here.

9. **Theorem A.5 and sentence images:** PDF p.58, “With the rule data
   above.” `RulePresentation.inference` is constructed from the actual
   ordered finite powers, premise pullbacks and coproducts. Product regular
   epis follow from pullback stability; `ruleMap_isPullback` proves the
   component base-change square, and coproduct regular-epi preservation
   supplies `inference_preservesRegularEpis`. Thus
   `RulePresentation.least_theorem_subobject` derives closure and leastness
   without an extra preservation assumption or stronger syntax assumptions.
   `sentenceImage_subobject` proves the exact image/pullback equality in
   an arbitrary regular category. Another agent independently inspected the
   pullback orientation, ordered modus-ponens premises and sentence-image
   comparison; no mathematical issue was found. The compiled first-order
   specialization receives the aggregate logical scheme morphism as data, so the seven syntax-derived scheme constructions remain open.

10. **Lemma 5.2:** PDF p.12, Lemma 5.2 (`lem:syntactic-functional-search`).
   `V46.SyntacticSearch.functional_search` constructs a graph-dependent
   production index with actual PA proofs of graph soundness and exact
   existential domain, then proves uniform graph equivalence from a proof
   of functionality in T. The selected index is independent of T. Its
   semantics use fair candidate/stage search at arbitrary elements of PA
   models, and the T-functional conclusion follows by completeness of T.
   No consistency or PA-functionality hypothesis is introduced. Another
   agent independently inspected this source argument, and production plus
   explicit checks passed strict compilation. The production `eventualGraph`
   presentation is explicit; comparison with the particular deterministic
   trace graph G of Lemma 5.1 remains a separate obligation. The external
   choice of an index in this pointwise lemma is not a proof of the uniform
   indexed sentence construction in Theorem 7.6.

## (E) Acceptance conditions, non-negotiable

These conditions concern a claim of a complete v46 formalization. The
implemented intermediate theorems may be delivered with their precise scope.

1. Compile every new public declaration, check the explicit manuscript types,
   and include all of them in the combined entry point and transitive allowed
   axiom audit. Failure rejects a claim that this new batch is verified.
2. Preserve the compiled typed-rule/image and occurrence-list constructions,
   and construct the remaining list identities, named-variable substitution
   and admissibility operations and concrete initiality instances in the
   required slices. Failure leaves Appendix A.3 and Section 5 incomplete.
3. Preserve the constructed chosen-splitting range functor, normalized source
   comparison and full abstract Theorem 4.2 under the final verifier. This
   condition has been met by targeted compilation; failure in the final
   integration would invalidate the verified-batch claim.
4. Construct standard and ultrapower soundness, the partial proof-search lift,
   the indexed theory family and uniform independent-sentence morphism.
   Failure leaves the new Section 6/7 categorical proof chain incomplete.
5. Implement the representation-independent Miller category and theory
   application with identical oracle-program domains as well as values.
   Failure leaves Section 8 incomplete.
6. Construct the Section 9 slice inference initiality and arbitrary c.e.-axiom
   theorem closure. Arbitrary idempotent splitting, the ordinary Karoubi
   equivalence and its natural source comparison are compiled; the separate
   unnumbered Karoubi restriction operation/preservation remain pending.
   Failure leaves these precise construction obligations open, without
   invalidating the numbered ordinary-equivalence result.

## (F) Not checked / uncertainty log

The numbered statements were inventoried by following every nested input of
`main.tex`. The review read the changed proofs, Section 3/4 definitions and
proofs, Appendix A's image argument, and the endpoint/cosheaf and faithful-family
constructions relevant to the changes. It did not perform a new line-by-line
correctness review of all 74 manuscript pages or all unchanged Lean sources.
No literature novelty claim was checked. No external registry verification,
independent-kernel replay, or numerical experiment is asserted.

Targeted Lake builds and strict `-DwarningAsError=true` replays passed for
the reviewed additions and their explicit statement checks. The eight modules
owned by this reviewer have per-command exit status 0 and source hashes in
`.codex-work/v46-correspondence-strict-dl76572p/results.json`; the other owners
also supplied strict-success evidence. Full integrated verifier evidence is
reported in the [implementation report](../V46_IMPLEMENTATION_2026-11-03.md)
and [verification record](../V46_VERIFICATION_2026-11-03.json); a source review
alone cannot establish that outcome.
The explicit checks contain categorical types. The Section 3/4 and image
theorem source signatures were inspected apart from their implementation
authors; independent reviews of the Karoubi and search constructions are
identified above. No small counterexample to the new
Section 3 or target logical-comparison statements was found; this is not an
exhaustive model search.

The reviewed production-source bytes are fixed by
[V46_REVIEW_SOURCE_SHA256.txt](V46_REVIEW_SOURCE_SHA256.txt), whose SHA-256 is
`a103ed257dd6f36938bfc5eaf0f2fbd801c02ca8c95b62b827c9095dca600c0a`. This is the
precommit source identity of the review; the implementation report identifies
the resulting commit and synchronization status.

Final self-audit: the strongest confirmed blocker to full completion is the
missing concrete predicate-category equivalence and T-provably total slice
evaluation/initiality realizations, and the representation-independent Miller
application. The strongest suspected but
unconfirmed issue is whether the old first-order coding and the manuscript's
named-variable/free-for presentation can be compared without additional
formal work beyond the currently identified obligations; no counterexample is
claimed. The most important unchecked material is the full concrete
standard/ultrapower arithmetic realization. The whole-paper recommendation
depends on these absent proof constructions, not on unavailable source files.
Final recommendation on a claim that **all v46 is formalized**: **reject unless
major reconstruction**. This does not reject the accurately scoped compiled
intermediate results.
