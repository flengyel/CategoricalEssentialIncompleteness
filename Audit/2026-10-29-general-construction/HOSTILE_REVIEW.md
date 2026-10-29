## (A) Kill-shots / hard blockers

This is an author-side mathematical audit, not a journal referee report. The object reviewed is the 13-page supplement **Finite proof algebras in range restriction categories**, dated 29 October 2026. The earlier note and its formalization are outside this audit.

Reviewed source: `general_recursion_category_construction.tex`, SHA-256 `3baa04a2cc03c2e1b50721aa9489b3687e6d7db1547f58c21cb618bbb99b3491`.

Reviewed PDF: `general_recursion_category_construction.pdf`, SHA-256 `f1dd251da1eff19f921f8c0d49489a2c6e24f0c96d0363542d00bfc450f6c550`.

**No fatal mathematical defect was confirmed in this version.** In particular, the Turing morphism has a substantive role in both the inseparability construction and the construction of partial folds. The note does not derive finite-stage domain unions from the Turing morphism, and it explicitly states that limitation.

The checked ambient data are restriction categories with extensional equality of arrows, their total subcategories, and their restriction-idempotent splittings. The deduction polynomial is a covariant endofunctor of a slice of the total category, with a specified extension to its partial slice. Proofs are its initial algebra; their conclusions have a computational range. No enriched category is asserted or needed.

The principal results were checked as follows. The anchors give printed page numbers, result labels, and source lines in the fingerprinted file.

| Result and anchor | Hypotheses actually used; proof check | Status |
| --- | --- | --- |
| Proposition 1.1, p. 2, `gen:turing`, lines 101–122 | Parameter universality represents the case-distinction arrow. Precomposition with the total pairing gives `dg=hg`. The separator inequalities then identify two complementary inverse-image domains. Nontriviality of `U` supplies the contradiction. Disjointness uses restriction zeros; preservation of the complementary join is used only along the total map `g`. | Checked. |
| Theorem 2.1, pp. 3–4, `gen:initial`, lines 182–258 | The partial inverse equations make every constructor stage a domain. For an arbitrary relatively total algebra on a split carrier, induction gives `x h_n=h_n` and `bar(h_n)=e_n`. A supported upper bound is therefore a total map from `(W,e)` to `(X,x)`. The algebra equation is checked after every `P(e_n)` and extended by the stated agreement union. The same agreement argument proves uniqueness. | Checked, including arbitrary split target carriers. |
| Lemma 3.1, pp. 4–5, `gen:section-inverse`, lines 275–296 | Universal ranges extend `γrγ=γ` and `bar(r)γ=γ` across `ran(γ)`. Hence `δ=r ran(γ)` satisfies both inverse equations. No unproved cancellation by a partial map is used. | Checked. |
| Proposition 3.2, p. 5, `gen:typed-coding`, lines 344–371 | An embedding of the entire one-step carrier into `U` gives `γ=⟨t,k⟩`. Lemma 3.1 supplies its restriction inverse. The partial-slice equation for that inverse follows by universal ranges. This construction does not presuppose an initial algebra. | Checked. |
| Corollary 3.3, p. 6, `gen:parameter-stability`, lines 390–418 | Every rule instance, premise, and conclusion retains the same parameter. Finite pullbacks and extensive coproducts identify the parameterized polynomial on a product carrier. Its stages are `1_K ⊠ e_n`. The gluing hypothesis ranges over algebras of the parameterized presentation, not merely product-shaped target algebras. | Checked under the expressly stated stable-union and parameterized-gluing hypotheses. |
| Lemma 4.1, pp. 6–7, `gen:recursion`, lines 452–488 | Universality constructs a total specialization map. Coding `U ⊠ U` into `U`, with a partial inverse on that image, permits the usual self-application calculation entirely as composites. The decoding identity is used only on encoded pairs. The resulting parameter map is total. | Checked, including partial definedness. |
| Theorem 4.2, pp. 7–8, `gen:turing-fold`, lines 542–592 | The diagonal-range filter makes the evaluator an arrow in the partial slice. Parameterized recursion supplies a code for the partial fold equation. Naturality is used only for a total code map. The resulting fixed point bounds every finite fold; restricting it to the separately assumed stage union gives precisely the support required by Theorem 2.1. | Checked. It removes the separate arrow-gluing assumption for the stated finitary polynomials. |
| Proposition 5.1, p. 9, `gen:numerical-regularity`, lines 651–669 | Finite limits and tagged sums stay within c.e. carriers. Images are c.e.; a surjection has a partial-recursive preimage selection total on its image. Hence image epimorphisms split, are regular, and remain regular under pullback. Monomorphisms are the computable injections, whose partial inverses are obtained by search. | Checked. |
| Lemma 6.1, pp. 10–11, `gen:theorem-image`, lines 777–795 | The rule polynomial preserves regular epimorphisms by products, pullbacks, and finite extensive sums. The structure map descends through the image of the proof conclusion map, making that image rule-closed. Any rule-closed subobject carries an algebra, so initiality proves leastness. | Checked. |
| Theorem 6.2, pp. 11–12, `gen:finite-valuation-consistency`, lines 797–889 | Decidable atom equality and list recursion construct valuations from finite lists of positive leaves. The explicitly defined decidable condition on proof/list pairs is closed under every constructor. Parameter-stable initiality makes it hold on all proof/list pairs. A proof and a refutation, evaluated using the concatenation of their positive lists, would give complementary Boolean values both equal to true. Extensivity and stable images turn this into the zero intersection of theorem and refutation domains. | Checked. No computable complement of the entire positive axiom domain is assumed. |
| Corollary 6.3, p. 12, `gen:essential`, lines 891–913 | The nullary proof maps put the two inseparable domains into the atom pullbacks of theorem and refutation domains. A consistent complete computational extension would give complementary pullbacks, contradicting inseparability. Rule closure of the extension is not required for this stronger statement. | Checked under the preceding construction hypotheses. |
| Proposition 7.1, p. 13, `gen:no-presheaf-range`, lines 953–973 | A selected range on a representable would represent a c.e. set `T`. The numeral summands imply `B⊆T`; factorization through every co-singleton excluding a number outside `B` implies `T⊆B`. Thus a non-c.e. `B` would be c.e. Only leastness of the putative selected range is used. | Checked. |

Two additional construction checks are important:

1. **Partial polynomial action.** Section 3, pp. 5–6, lines 311–342, defines the object action and the action on total slice arrows before discussing partial maps. The sufficient extension conditions make the polynomial preserve the distinguished left legs of domain spans and the pullbacks used in their composition. Restriction is preserved by applying the same functor to the domain inclusion. Thus the partial-arrow action is a restriction functor; it is not merely a set-level operation on codes.
2. **Finite polynomial preservation of the stage union.** Section 3, p. 6, lines 378–388, separately requires preservation by restriction products, total inverse image, and the relevant finite coproducts. Product stability gives the finite multi-index union; increasing stages make diagonal indices cofinal. Pullback and coproduct preservation then give the union of the polynomial images. The argument does not infer arbitrary inverse-image preservation from product stability alone.

## (B) Major weaknesses

**No unresolved major defect is confirmed under the claims actually stated.** The following are boundaries of the result, not silently supplied lemmas.

- **Stage-domain existence remains conditional.** Theorem 4.2, p. 8, states “If the finite-stage domains have the two unions”; Problem 7.2, p. 13, asks for their construction from categorical iteration. The fixed point obtained from the Turing morphism need not have exactly the finite-stage domain. The proof correctly restricts it to a union whose existence has been assumed. Failure mode for any stronger claim would be `unproved`; evidence is `absence_in_text`, together with the explicit conditional statements. The current note does not make that stronger claim.
- **The class of categories is narrower than all recursion categories.** Theorem 6.2 requires regularity, extensivity, agreement of computational ranges with regular images, decidable equality, and parameter-stable finite recursion. The agreement-of-images assumption makes every subobject of the total category computational, as Section 6 explicitly observes. It cannot simply be transported to a category with arbitrary noncomputational presheaf subobjects. The numerical model is verified; applicability to other recursion categories remains a separate theorem.
- **The arithmetic comparison has not been supplied.** Corollary 6.3 concerns the constructed propositional presentation and computational extensions represented by domains of its syntax object. No interpretation of Robinson arithmetic, PA, or an arbitrary c.e. arithmetic extension is constructed in this supplement. Nor is a conservativity or reflection theorem supplied that would transfer this result to those theories. An assertion that the supplement already recovers those arithmetic theorems would be `unsupported_generalization`, with evidence `absence_in_text`. The supplement itself makes no such assertion.

These limitations prevent the audit from certifying realization of the full Di Paola–Heller program. They do not refute the conditional construction proved here.

## (C) Minor issues

No mathematical correction is required on the basis of this audit. Prose, typography, and document layout are being reviewed separately.

The numerical section gives an independent dovetailing construction of folds after the abstract Turing construction. This is mathematically consistent and useful as a realization check: it does not assert that arbitrary externally indexed countable families of partial recursive maps have computable joins. Its indices arise uniformly from the fixed constructor and algebra data.

The phrase “computational theory” in Corollary 6.3 is accompanied by an explicit closure definition. It should retain that definition when quoted elsewhere; identifying it with an arbitrary first-order theory requires the separate comparison discussed above.

## (D) Cross-section consistency failures

**No unresolved cross-section inconsistency was found.** The following sensitive interfaces were checked explicitly.

| Interface | Check |
| --- | --- |
| Zero versus nullary constructors | Restriction zeros are explicit. The functor `P` need not preserve zero, so `P(e_0)` can contain nullary constructors. The induction in Theorem 2.1 does not accidentally erase them. |
| Ambient evaluation versus typed evaluation | Section 4 does not assume that a Turing morphism automatically lives in every partial slice. It filters the ambient evaluator by the range of the type diagonal. Universal ranges give `π₁r=π₂r`; the filter fixes any already well-typed specialization. |
| Strength versus partial parameter maps | Equation (6), p. 7, is restricted to total code maps. This restriction is necessary: a nullary summand forgets its parameter, so the corresponding equation need not hold for an undefined partial parameter map. The proof uses only the valid total case. |
| Partial fixed point versus total finite fold | The fixed point may have a larger domain than the union of finite stages. Section 4 restricts it to that union, and Section 7 expressly preserves this distinction. |
| Abstract gluing versus Turing-derived gluing | Theorem 2.1 gives an abstract criterion. Theorem 4.2 supplies its arrow-upper-bound hypothesis for finitary rule polynomials. Corollary 3.3 is consequently available under stable stage unions, as stated after Theorem 4.2. |
| Domain lattices versus ordinary subobjects | Section 6 expressly derives their coincidence from its strong regular-image assumption. Section 7 uses only selected presheaf subobjects and does not claim coincidence with all presheaf subobjects. |
| Selected bottom versus empty presheaf | Section 7 assumes every initial map belongs to the distinguished mono class before identifying the selected bottom with `y0`. It explicitly warns that `y0` need not be the empty presheaf. The no-range proof does not assume zero preservation by Yoneda. |
| Source attribution versus novelty | The general existence of recursion categories without ranges is credited to Heller before the selected-presheaf calculation. No novelty claim for that general obstruction appears. |

These checks include previously identified draft risks. The final source contains the required restrictions or hypotheses; the report does not downgrade an unresolved earlier blocker by interpreting the text more favorably.

Sanity tests included the identity endofunctor, a constant functor with nullary constructors, ordinary partial maps with genuine unions, and the uniformly computable numerical instance. The zero-stage and arbitrary split-target cases behave as the proofs require. A trivial category cannot satisfy the nontriviality hypothesis used for inseparability. No claim that the full Turing hypotheses hold for every category of partial maps was used in these tests.

## (E) Acceptance conditions, non-negotiable

The following conditions concern the mathematical scope of this supplement. The current fingerprint satisfies conditions 1–4. Conditions 5–6 govern stronger future claims, not acceptance of the present conditional result.

1. **Preserve the exact initiality hypotheses.** Deliverable: Theorems 2.1 and 4.2 must state the two stage-domain unions and the relevant parameter stability. Endpoint: the fold proof uses a specified union with exact support and covers arbitrary split target algebras. Removing these without a replacement proof would invalidate acceptance of initiality.
2. **Preserve the typed evaluator and total-parameter restriction.** Deliverable: the diagonal-range filter and equation (6). Endpoint: the specialized evaluator is a partial-slice arrow, and every parameter map used in the strength equation is total. Failure would invalidate Theorem 4.2 as written.
3. **Preserve the finite-valuation consistency construction.** Deliverable: Theorem 6.2, including regular-image compatibility, list recursion, decidable equality, and parameter-stable initiality. Endpoint: the proof/refutation pullback is initial without a global computable valuation separating the two atomic domains. Replacing this with an assumed consistency condition would remove the constructed-theory result.
4. **Keep completion claims relative to selected domains.** Deliverable: Section 7 with its selected mono class, bottom qualification, and explicit no-range argument. Endpoint: no preservation of ranges, computational theorem images, or logical zero is inferred merely from full faithfulness of Yoneda. Failure would invalidate the proposed completion application.
5. **For an unconditional recursion-category theorem, construct the stage unions.** Deliverable: a categorical iteration theorem with a finite-tree evaluator whose termination domain is exactly the stage union, including stability and polynomial preservation. Endpoint: Theorem 4.2 can be applied without postulating those unions. Without this deliverable, retain the conditional scope; reject an unconditional reformulation.
6. **For recovery of arithmetic essential incompleteness, supply typed comparison data.** Deliverable: an explicit interpretation of the intended arithmetic theories and their c.e. extensions, with the necessary preservation or reflection of deduction, consistency, and completeness. Endpoint: a stated arithmetic theorem follows from Corollary 6.3 rather than from a separately imported incompleteness theorem. Without this deliverable, drop the arithmetic-recovery and full-program-realization claims.

## (F) Not checked / uncertainty log

- This is a mathematical source audit, not a Lean verification. No claim that these new theorems have been formalized is certified.
- No literature-wide novelty search was performed. The note makes no “first” or uniqueness claim requiring one.
- Garner and Lin's selected-presheaf definition and Lemma 9 were independently checked in their primary text, [*Cocompletion of restriction categories*](https://arxiv.org/pdf/1610.07164), Section 3.1 and Lemma 9. They support the selected-subobject comparison used in Section 7.
- After the initial audit, this reviewer independently inspected Heller's original scan at printed pp. 1261–1262 and 1267, covering the range and stable-union definitions and the cited example. Several printed typing errors on p. 1262 were confirmed; none is used by the supplement. The exact discrepancies, typed replacements, and dependency check are recorded in `HELLER1990_TARGETED_SOURCE_CHECK.md`. This was a targeted inspection, not a rereading or validation of Heller's entire paper.
- The full relation to the original Di Paola–Heller program, and recovery of particular arithmetic incompleteness theorems, remain unchecked because the required comparison constructions are absent from this supplement. This is the most important scope limitation.
- Existence of the stated regularity, decidable-equality, and stable-domain-union structures in general nonnumerical recursion categories remains open here. The numerical realization was checked directly.
- Document rendering and the absence of build warnings are outside this mathematical audit.

**Strongest confirmed blocker:** none for the conditional theorems in the fingerprinted supplement. An assertion that it already realizes the full arithmetic program would be blocked by the absent comparison theorem.

**Strongest suspected but unconfirmed blocker:** no specific false statement or counterexample is currently identified. The main unresolved risk is whether a sufficiently broad class of nonnumerical recursion categories satisfies the stage-union and valuation hypotheses without losing the intended computational domains.

**Most important unchecked item:** the interpretation connecting the constructed computational propositional theories with the intended arithmetic theories and their c.e. extensions.

**Dependence on unavailable material:** the correctness assessment of the stated conditional results does not require unavailable material. A verdict on the full program would require additional comparison constructions and a fuller audit against its original sources.

**Final recommendation: unknown.** No fatal or major mathematical defect was confirmed in the present conditional supplement. This does not certify novelty, journal suitability, or completion of the Di Paola–Heller program.


## Heller source follow-up

The targeted scan inspection is recorded in [HELLER_SOURCE_CHECK.md](HELLER_SOURCE_CHECK.md). The reviewer independently confirmed the three substantive typing discrepancies on p.1262. None is invoked as an unproved formula in this supplement. The source fingerprint and conditional audit conclusion remain unchanged. This follow-up is not a complete errata list for Heller.
