# Complete audit of version 29

All 31 references identify real works. No invented reference was found. Version 29 contains one incomplete attribution of a theorem's hypotheses and a publication-year ambiguity. These are corrected in version 30. One original-text verification remains open, so the citation audit is not reported as complete without qualification.

## Scope and coverage

The audit used only *Logical consequence and essential incompleteness in recursion categories*, version 29, 1 November 2026, at repository commit `d33629db31ba0e9ea298a05c0230f661ec8b174b`. The corresponding source archive and PDF were retrieved before review. The separate note and earlier paper versions were excluded.

Two hostile-referee reviewers read all mathematical sections and appendices; their coverage comprises all 62 numbered theorems, propositions, lemmas and corollaries. The mathematical-writing reviewer read every compiled source file: 22 TeX files, 6,862 lines, including the abstract, introduction, nested inputs, appendices and bibliography. The writing report gives the actual outline, definition and type checks, and the function of 363 paragraph groups. It consulted Knuth, Larrabee and Roberts's *Mathematical Writing*, Section 1 and Sections 4–5.

The citation inventory contains 31 bibliography entries and 65 individual uses. Four citation reviews reconcile exactly to that inventory. Each use has its source location, supporting passage or argument, source version, status and correction in the accompanying ledger. Publication metadata and support for the cited claim are checked separately.

## Findings and corrections

### Di Paola–Heller: a hypothesis was omitted

At introduction line 120, version 29 attributes recursive inseparability to dominical recursion categories in which every morphism has a section. The cited Theorem 8.15 also assumes the compatible coproduct conditions of Definition 7.1. Definition 6.2 supplies only the section condition.

The corrected attribution explicitly requires binary coproducts for which coproducts of total morphisms are total and the near product distributes over coproducts. The original journal text was checked at Definition 6.2, p. 612; Definition 7.1, p. 615; and Theorem 8.15, p. 625. The correction passed a separate recheck. This repairs a historical attribution; it does not change the comparison theorem proved in this paper.

### Hájek–Pudlák: publication and copyright dates were conflated

The Cambridge edition's frontmatter prints copyright 2016, while Cambridge's publication record gives 2 March 2017 for print and 24 March 2017 for the digital edition. The corrected bibliography uses 2017 and identifies the Springer text as originally published in 1993. The propositional schemes match numbered paragraph 0.10, p. 7; the locator now says this rather than “Section 0.10”.

Primary records: [Cambridge publication record](https://www.cambridge.org/core/books/metamathematics-of-firstorder-arithmetic/E72D370D90F316D86CB9D0927377A1A3), [edition frontmatter](https://assets.cambridge.org/97811071/68411/frontmatter/9781107168411_frontmatter.pdf), and [propositional schemes](https://assets.cambridge.org/97811071/68411/excerpt/9781107168411_excerpt.pdf).

### Hirst–Hirst: the equality schemes are adapted forms

The source prints variable reflexivity and substitutivity principles. The paper uses the corresponding schemes with terms as parameters and explicit admissibility conditions. The attribution now states this distinction. No axiom, side condition, constructor or proof was changed. The quantifier and equality passages were checked in Sections 2.11–2.12 and 3.1 of the [authors' text](https://www.appstate.edu/~hirstjl/primer/hirst.pdf), and the corrected attribution passed recheck.

### Categorical terminology

Seven categorical uses of “map” were replaced by “morphism”: zero morphisms, the coproduct comparison and product comparison morphisms, the Turing parameter morphism, the free-variable and formula-substitution morphisms, and the premise/conclusion morphisms. Numerical functions, functions between hom-sets, and the established expression “partial-map category” retain their appropriate terminology.

No theorem hypothesis was removed, no application was dropped, and no mathematical proof was shortened. The optional opening-paragraph rewrite and other optional writing changes were left for the reserved introduction/abstract revision.

## Citation verification results

All 31 bibliographic identities and the asserted publication details were checked. After the corrections, 64 of the 65 uses have supporting primary text. This count includes explicit qualifications for author versions, equivalent formulations, and adaptations; it does not falsely describe those as quotations from a published version.

The detailed checks include the following distinctions.

- Miller's stronger same-index property is present immediately after Theorem 6.3 in the author's text and explicitly in Bauer–Hanson version 3, Theorem 2.2. Their approximation convention agrees with the convention used here. The proof audit's dependency on this stronger statement is closed.
- The version 10 erratum was checked at the exact cited GitHub commit. Its main theorem is Theorem 6.4 on p. 11. No later revision was substituted.
- Heller's original inverse-image signature has a printed variance typo. The paper's contravariant signature is correct; the source typo was not copied.
- The fixed arithmetic coding lemma uses consequences of Montagna's formalized enumeration and parameterization construction. Its citation is not a claim that Montagna prints every displayed graph equation verbatim. The foundation reviewer found no missing proof on this ground.
- The range-category references retain their additional regularity hypotheses; a split range factorization is not identified with a regular-image factorization without those hypotheses.
- The three binding references all support their attribution concerning identification up to renaming bound variables. Their settings are distinguished from the paper's raw named syntax.

The per-use ledger retains both the version 29 status and the status after correction. The bibliography ledger records the checked metadata separately. The complete review archive contains all four citation reports, both hostile-referee reports, the mathematical-writing report and its paragraph inventory, the correction diff, and the rechecks.

## Open verification: Cockett 1990

J. R. B. Cockett, *List-arithmetic distributive categories: Locoi*, Journal of Pure and Applied Algebra 66(1) (1990), 1–29, [DOI 10.1016/0022-4049(90)90121-W](https://doi.org/10.1016/0022-4049(90)90121-W), is a real publication with correct bibliography metadata.

Its original full text could not be obtained through the publisher, author-linked records, public repositories or Library searches. Appendix A's contextual attribution of parameterized list recursion is corroborated by Maietti's primary text, Definition 2.4 and the following paragraph, but it has not been independently checked in Cockett's article. This one use is explicitly marked as not directly verified. The article is retained as a precedent; it was not deleted to make the audit appear closed. A copy of the original article is needed to finish this check.

## Proof, prose and production conclusions

Neither hostile-referee reviewer found a confirmed mathematical blocker after reading the complete assigned source. The writing review found no required reconstruction, missing major definition, invented technical construction, or editorial-process paragraph in the compiled manuscript. These are results of the stated reviews, not a claim of formal certification or guaranteed absence of errors.

The corrected passages passed the source, citation and writing rechecks. The paper remains 77 pages and the standalone appendix 10 pages. Their final LaTeX logs contain no undefined references, undefined citations, overfull boxes or warnings. The changed rendered pages were inspected. No Lean files were changed or checked.

Version 30 contains the corrections; version 29 remains the frozen audit basis. The full-text access gap above prevents an unqualified statement that every citation has passed direct original-source verification.
