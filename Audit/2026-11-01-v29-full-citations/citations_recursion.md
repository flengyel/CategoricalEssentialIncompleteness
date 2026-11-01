# Version29 citation audit: recursion literature

Scope: eight references, **29 individual uses**, reconciled exactly to the frozen inventory. No manuscript was edited. All eight works exist; primary claim-bearing text was obtained and read for every work. No existence or full-text status remains unresolved.

## Required correction

**Introduction line120, DPH Theorem8.15:** add compatible binary coproducts to the summarized hypotheses. The theorem assumes c+-dominicality, not merely the choice axiom. Definition6.2 (p612) supplies the choice condition; Definition7.1 (p615) additionally requires pairwise coproducts, totality of f+g for total f,g, and invertibility of the canonical distributivity map (X×Y1)+(X×Y2)→X×(Y1+Y2). A minimal repair is:

> Di Paola and Heller proved recursive inseparability in dominical recursion categories with compatible binary coproducts and a section for every morphism.

## Citation precision, not a demonstrated mathematical error

**Syntactic category line83, Montagna pp108/115:** p108 asserts the categorical structure, universal evaluator and formalized s-m-n; Note1 p115 fixes the arithmetic graph coding. The source does not separately print the full uniform PA-provable functionality and composition equations displayed in the current Lemma5.1. The citation supports the standard construction; a formalized enumeration/composition source or a short coding proof would make every displayed equation directly traceable. The source should not be described as stating those equations verbatim.

## Bibliography and source versions

All eight bibliography entries have correct identity, author, title, year, venue, volume and pages as applicable. Missing DOIs below are optional additions, not false metadata. Composition’s unversioned arXiv link currently yields **v2**, whose Corollary2 is on p5. The cited erratum was checked at the exact immutable commit; its compiled main theorem is **Theorem6.4, p11**, not Theorem6.3. Its TeX author field is empty, but its repository identifies the work as Florian Lengyel’s corrections. The source/date/version10 and repository provenance agree.

|Key|Verified publication/version|DOI|Primary text route|
|---|---|---|---|
|Bernardi|Claudio Bernardi; 1986; Proceedings of the American Mathematical Society 98(1), 124–134|10.1090/S0002-9939-1986-0848889-9|Primary scanned article, author-uploaded by Claudio Bernardi; complete claim-bearing pages 125–128 read in browser full-text transcription. Publisher index corroborates publication. AMS PDF 403; author PDF download link 404. Library title/content searches found no Bernardi scan.|
|DPH|Robert A. Di Paola, Alex Heller; 1987; The Journal of Symbolic Logic 52(3), 594–635|10.2307/2274352|Publisher metadata plus original journal scan from Library libfile_d063c67205808191b249e7ada90406e6; JSTOR cover sheet is PDF page 1; printed p594 is PDF page2. Text read at all attributed locations and prerequisite Definitions6.2/7.1. Theorem8.15 page visually checked.|
|DPM|Robert A. Di Paola, Franco Montagna; 1991; The Journal of Symbolic Logic 56(2), 643–660|10.2307/2274707|Publisher metadata plus original journal scan from Library libfile_a3e838b0cf608191941681da53d286df. Cover sheet PDF1; printed p643 PDF2. Claim-bearing pp644–646 and657–658 read; Corollary4.4 page visually checked.|
|Heller|Alex Heller; 1990; The Journal of Symbolic Logic 55(3), 1252–1268|10.2307/2274486|Publisher metadata plus original journal scan from Library libfile_528c1ed3c574819190db2ba23814c0bf. Cover sheet PDF1; p1252 PDF2. Sections3,5,6,8,9 read; pp1260–1261 visually checked to distinguish real printed typographical errors from OCR.|
|Lengyel2004|Florian Lengyel; 2004; Annals of Pure and Applied Logic 125(1–3), 1–41|10.1016/S0168-0072(03)00060-5|Publisher metadata plus original image-only journal scan from Library libfile_45e2646c443c8191be5596ee7488b7d0. Library filename said2003; journal running head explicitly125(2004)1–41. Renamed local scan to its publication year. OCR of original abstract and sections3–4, especially Theorem26 p27 and ensuing proof p28–30. Publisher PDF route returned HTML, not PDF.|
|Corrections|Florian Lengyel; 2026; author-maintained correction manuscript; version10; commit5555e4fa1da7b8e3a0836dd1fbf1ca385cacd03b|none asserted|GitHub connector fetched exact cited commit and path, blob841d43806db321076744f1d6ed8378f7ac14f29f. Commit date20October2026 verified. Source title/date version10 verified; author field blank, but repository README identifies corrections as by Florian Lengyel and copyright2026. Library zip libfile_4ef06b9f72bc81918985a600a9bdc8f0 contains same source apart from terminal newline, plus compiled30page PDF. Main result read in source and compiled PDF Theorem6.4 p11.|
|Composition|Florian Lengyel; 2026; arXiv [math.LO]; arXiv2609.25556v2, submitted1October2026; document dated30September2026|10.48550/arXiv.2609.25556|Author repository and primary arXiv record found by authoritative search. Browser arXiv open disabled, but direct public arXiv PDF downloaded successfully using urllib; title page identifies v2. Corollary2 p5 read in PDF text, together with Theorem1 and proof pp4–5. Maintained author v37 TeX also fetched, blob3027cd18bbf55b7881c41fa233007703e27c638a; arXiv PDF is controlling source.|
|Montagna|Franco Montagna; 1989; Notre Dame Journal of Formal Logic 30(1 (Winter1989)), 105–116|10.1305/ndjfl/1093634998|Original journal scan from Library libfile_b164ab3413c48191a48dcccaed3df4a8; printed105 PDF1, no cover sheet. Header gives Winter1989, overriding secondary metadata reporting1988 online date. All cited pp105–106,108–109,114–115 read, Note1 visually checked. ProjectEuclid landing route returned iframe then security check; existence and metadata verified from primary scan.|

## Every citation use

Each entry below records its actual source locus. “Supported” means the source’s assumptions and scope fit the attributed claim; it does not attribute adjacent new constructions to that source.

### Bernardi — sections/08-essential-incompleteness-of-arithmetic.tex:328
Status: **supported**. Cited locator: pp.~125--126. Actual locus: **p125, final numerical definition/example; p126, Proposition2(b)**.
Evidence: https://www.researchgate.net/publication/303491669_Precomplete_equivalence_relations_in_dominical_categories
The source defines numerical precompleteness exactly as totalization modulo R, lists PA-provable equality of program indices, and states distinct classes recursively inseparable. The manuscript consequence for disjoint nonempty unions follows by selecting one class in each; a separator of unions would separate those classes.

### Bernardi — sections/01-introduction.tex:123
Status: **supported**. Cited locator: pp.~125--128. Actual locus: **pp125–126, numerical example/Proposition2; p128, Theorem2**.
Evidence: https://www.researchgate.net/publication/303491669_Precomplete_equivalence_relations_in_dominical_categories
The cited span contains the PA example and the categorical inseparability theorem. Theorem2 is for nonzero disjoint unions of classes in a c+-dominical recursion category; the manuscript makes a historical attribution and does not apply it to arbitrary restriction categories.

### DPH — sections/01-introduction.tex:99
Status: **supported**. Cited locator: pp.~594--595. Actual locus: **§1, pp594–595, especially numbered assertions(3),(5) and discussion after them**.
Evidence: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/dominical-categories-recursion-theory-without-elements1-2/2E11506A81794B06EF34603881D79394
The introduction explicitly places recursive/effective inseparability of theorem and refutable sets among the generalized incompleteness formulations and proposes a categorical development to obtain corresponding domains.

### DPH — sections/01-introduction.tex:108
Status: **supported**. Cited locator: none. Actual locus: **§1 p594; §2 pp597–599**.
Evidence: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/dominical-categories-recursion-theory-without-elements1-2/2E11506A81794B06EF34603881D79394
The opening states the new abstract recursion-theoretic program, and §2 introduces the dominical axioms. Historical attribution is accurate.

### DPH — sections/01-introduction.tex:120
Status: **hypothesis_omitted**. Cited locator: Theorem 8.15. Actual locus: **Theorem8.15 p625; Definition6.2 p612; Definition7.1 p615**.
Evidence: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/dominical-categories-recursion-theory-without-elements1-2/2E11506A81794B06EF34603881D79394
Theorem8.15 proves the two diagonal halting domains inseparable in a c+-dominical setting with a Turing morphism. Having a section for every morphism supplies c-dominicality only. Definition7.1 also requires compatible binary coproducts, including preservation of total maps by + and distributivity of the near product. The manuscript summary omits this additional hypothesis.
Required correction: Replace with “Di Paola and Heller proved recursive inseparability in dominical recursion categories with compatible binary coproducts and a section for every morphism [Theorem8.15].”

### DPM — appendices/d-faithful-family.tex:60
Status: **supported**. Cited locator: Corollary 4.4, pp.~657--658. Actual locus: **Corollary4.4, pp657–658**.
Evidence: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/some-properties-of-the-syntactic-precursion-categories-generated-by-consistent-recursively-enumerable-extensions-of-peano-arithmetic/CEBD30B1664AF179CF873E007F2113F8
Corollary4.4 states no S_T is locally connected, under the consistent r.e. PA-extension setup. Its proof treats Σ1-sound and nonsound T separately. The manuscript correctly concerns unprimed S_T; its comment about target connected domains is its own construction.

### DPM — sections/05-syntactic-recursion-category.tex:47
Status: **supported**. Cited locator: p.~644. Actual locus: **p644, notation paragraph before §1**.
Evidence: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/some-properties-of-the-syntactic-precursion-categories-generated-by-consistent-recursively-enumerable-extensions-of-peano-arithmetic/CEBD30B1664AF179CF873E007F2113F8
The PR-extension notation paragraph explains how formulas with primitive-recursive symbols are replaced by formulas of PA preserving free variables and provability. The Σ1 graph formula in the manuscript is its explicit deterministic trace construction; it is not a quotation of DPM.

### DPM — sections/05-syntactic-recursion-category.tex:114
Status: **supported**. Cited locator: none. Actual locus: **§1 p646, definitions of objects and uniform equality; Montagna pp105–106**.
Evidence: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/some-properties-of-the-syntactic-precursion-categories-generated-by-consistent-recursively-enumerable-extensions-of-peano-arithmetic/CEBD30B1664AF179CF873E007F2113F8
DPM extends Montagna’s set-based unprimed presentation to T. Object terms versus their interpreted sets are the manuscript’s explicit equivalent presentation, not a new assertion attributed verbatim to DPM. Uniform function equality matches graph equivalence using PA-provable functionality.

### DPM — sections/05-syntactic-recursion-category.tex:133
Status: **supported**. Cited locator: none. Actual locus: **p646, separate displayed definition of pointwise equality for S′_T**.
Evidence: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/some-properties-of-the-syntactic-precursion-categories-generated-by-consistent-recursively-enumerable-extensions-of-peano-arithmetic/CEBD30B1664AF179CF873E007F2113F8
The source defines pointwise equality by a separate T-proof for each standard input. T=PA gives Montagna’s S′. V29 immediately corrects the original authors’ category assertion using Composition, and does not rely on the primed category existing.

### DPM — sections/01-introduction.tex:46
Status: **supported**. Cited locator: none. Actual locus: **pp643–646, especially definition of S_T p646**.
Evidence: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/some-properties-of-the-syntactic-precursion-categories-generated-by-consistent-recursively-enumerable-extensions-of-peano-arithmetic/CEBD30B1664AF179CF873E007F2113F8
The historical syntactic category attribution and uniform provable-equality description match the unprimed construction. The ensuing model-family and section-lift assertions are the current manuscript’s results, not assigned to DPM by this citation.

### DPM — sections/01-introduction.tex:52
Status: **supported**. Cited locator: Corollary 4.4. Actual locus: **Corollary4.4, pp657–658**.
Evidence: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/some-properties-of-the-syntactic-precursion-categories-generated-by-consistent-recursively-enumerable-extensions-of-peano-arithmetic/CEBD30B1664AF179CF873E007F2113F8
No S_T is locally connected for consistent computably enumerable T extending PA. Hypotheses and unprimed scope match exactly.

### DPM — sections/01-introduction.tex:102
Status: **supported**. Cited locator: none. Actual locus: **Introduction p644, paragraph beginning “Also, the study…”**.
Evidence: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/some-properties-of-the-syntactic-precursion-categories-generated-by-consistent-recursively-enumerable-extensions-of-peano-arithmetic/CEBD30B1664AF179CF873E007F2113F8
DPM explicitly discusses Heller’s local-connectedness hypothesis, contrasts the syntactic examples, and asks for a more general theorem. This supports the historical motivation claim.

### Heller — sections/02-categorical-preliminaries.tex:20
Status: **supported**. Cited locator: Section~5. Actual locus: **§5 pp1260–1261, domain calculus**.
Evidence: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/an-existence-theorem-for-recursion-categories/5A24053486108F86AF005D88D63D40E8
Heller calls endomorphisms equal to their domains domains; domdomφ=domφ and φ=φdomφ appear in the domain calculus. Restriction-idempotent is the current Cockett–Lack terminology, accurately identified with Heller’s domains.

### Heller — sections/02-categorical-preliminaries.tex:50
Status: **supported**. Cited locator: Section 6. Actual locus: **§6 p1261, first paragraph**.
Evidence: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/an-existence-theorem-for-recursion-categories/5A24053486108F86AF005D88D63D40E8
The source explicitly defines ε receiving φ by εφ=φ, and range by the arrow-agreement property before observing leastness. V29 preserves that substantive agreement law. Its inverse-image typing is correct; see source-typo note in report.

### Heller — sections/02-categorical-preliminaries.tex:165
Status: **supported**. Cited locator: Section 9. Actual locus: **§9 pp1264–1265, definition before Lemma9.1**.
Evidence: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/an-existence-theorem-for-recursion-categories/5A24053486108F86AF005D88D63D40E8
Heller defines a Turing morphism W×X→Y by parameterization of arbitrary V×X→Y using a total V→W, and a recursion category as a prodominical isotype with such a morphism. V29 takes W=X=Y=U; its extra mention of binary restriction products records the P-category structure.

### Heller — sections/01-introduction.tex:100
Status: **supported**. Cited locator: Sections 8--9. Actual locus: **§8 p1264 Lemma8.2/Proposition8.4; §9 p1265 Theorem9.2**.
Evidence: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/an-existence-theorem-for-recursion-categories/5A24053486108F86AF005D88D63D40E8
Local connectedness is an explicit hypothesis for composition of developments and in the main existence theorem. V29 states only that it enters that theorem and is accurate.

### Heller — sections/01-introduction.tex:110
Status: **supported**. Cited locator: Section 5. Actual locus: **§5 pp1260–1261**.
Evidence: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/an-existence-theorem-for-recursion-categories/5A24053486108F86AF005D88D63D40E8
Heller explicitly adopts Rosolini P-categories and names their pointed version prodominical categories. Historical assertion matches source.

### Heller — sections/09-three-point-space.tex:119
Status: **supported**. Cited locator: Section 3. Actual locus: **§3 p1256, frame definition continuing on p1257**.
Evidence: https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/an-existence-theorem-for-recursion-categories/5A24053486108F86AF005D88D63D40E8
A frame consists of chosen isomorphisms X→X×X, X→X+X, X→X# and their inverses. V29 lists exactly those six maps. Existence of its concrete fork isomorphisms is proved locally and is not supplied by Heller.

### Lengyel2004 — sections/01-introduction.tex:104
Status: **supported**. Cited locator: none. Actual locus: **§4 p27, Theorem26; definitions immediately before it; proof pp28–30**.
Evidence: https://www.sciencedirect.com/science/article/pii/S0168007203000605
The primary theorem asserts recursion-category completion when the source is separated by an iteration functor: the functor is faithful and its target separated. Uniform generation, isotypicality and iteration-category assumptions are explicit. V29’s broad historical sentence is accurate; it does not claim those hypotheses suffice for its distinct criterion.

### Corrections — sections/01-introduction.tex:104
Status: **supported**. Cited locator: none. Actual locus: **exact cited commit; Introduction p1; §1.2 p3; Theorem6.4 p11**.
Evidence: https://github.com/flengyel/errata/blob/5555e4fa1da7b8e3a0836dd1fbf1ca385cacd03b/lengyel2004/lengyel2004_repairs_v10.tex
Version10 gives corrected existence proofs with a faithful iteration functor into a separated iteration category; Theorem6.4 states the relative completion theorem. Exact cited commit/date/version and bibliography title verified. No later erratum version substituted.

### Composition — sections/05-syntactic-recursion-category.tex:135
Status: **supported**. Cited locator: Corollary 2. Actual locus: **arXiv2609.25556v2, Corollary2 p5, following Theorem1 pp4–5**.
Evidence: https://arxiv.org/abs/2609.25556
Corollary2 states precisely that for every consistent r.e. T⊇PA, proposed S′_T composition is not representative-independent, already on partial maps ω⇀ω; T=PA includes S′. Theorem1/proof constructs the unequal composites. V29 matches its hypotheses and scope.

### Montagna — sections/05-syntactic-recursion-category.tex:35
Status: **supported**. Cited locator: p.~115, Note~1. Actual locus: **p115, Note1**.
Evidence: https://projecteuclid.org/journals/notre-dame-journal-of-formal-logic/volume-30/issue-1/Pathologies-in-two-syntactic-categories-of-partial-maps/10.1305/ndjfl/1093634998.full
Note1 fixes Δ0 formulas for Kleene’s computation predicate and the primitive-recursive output function, with graph abbreviation ∃z(T(n,x,z)∧U(z,y)). V29’s Tr/out notation is the same standard computation coding; PA formalized properties are discussed separately in its next lemma.

### Montagna — sections/05-syntactic-recursion-category.tex:83
Status: **supported_with_precision_note**. Cited locator: p.~108; p.~115, Note~1. Actual locus: **p108, first paragraph and Turing-morphism paragraph; p115, Note1**.
Evidence: https://projecteuclid.org/journals/notre-dame-journal-of-formal-logic/volume-30/issue-1/Pathologies-in-two-syntactic-categories-of-partial-maps/10.1305/ndjfl/1093634998.full
The source asserts the pointed p-category structure, the universal evaluator, and formalized s-m-n; Note1 fixes its arithmetic graph formulas. This supports the standard formalized construction used by the lemma. It does not print all displayed uniform functionality/composition/specialization graph equations separately.
Precision note: For fully explicit provenance of every displayed PA theorem, cite a formalized enumeration/composition theorem or add a short proof for the chosen coding. Do not say Montagna states all these equations verbatim.

### Montagna — sections/05-syntactic-recursion-category.tex:111
Status: **supported**. Cited locator: p.~105. Actual locus: **p105, object definition item1**.
Evidence: https://projecteuclid.org/journals/notre-dame-journal-of-formal-logic/volume-30/issue-1/Pathologies-in-two-syntactic-categories-of-partial-maps/10.1305/ndjfl/1093634998.full
Objects are the smallest class containing ω and closed under Cartesian products and tagged disjoint unions A×{0}∪B×{1}. V29 matches exactly.

### Montagna — sections/05-syntactic-recursion-category.tex:114
Status: **supported**. Cited locator: none. Actual locus: **p105, object/morphism definitions; p108, structure; p115, Note1**.
Evidence: https://projecteuclid.org/journals/notre-dame-journal-of-formal-logic/volume-30/issue-1/Pathologies-in-two-syntactic-categories-of-partial-maps/10.1305/ndjfl/1093634998.full
The unprimed presentation uses program indices modulo universally PA-provable partial-function equality with the specified computation formulas. V29’s object-term equivalence is its own elementary recoding of this presentation, using the same codings.

### Montagna — sections/05-syntactic-recursion-category.tex:133
Status: **supported**. Cited locator: none. Actual locus: **p106, opening definition of S′**.
Evidence: https://projecteuclid.org/journals/notre-dame-journal-of-formal-logic/volume-30/issue-1/Pathologies-in-two-syntactic-categories-of-partial-maps/10.1305/ndjfl/1093634998.full
Montagna’s primed equality requires, for each standard input, a PA proof of the same convergence/output statement. It agrees with DPM’s T=PA specialization. V29 correctly rejects the original category claim on the independent Composition result.

### Montagna — sections/05-syntactic-recursion-category.tex:149
Status: **supported**. Cited locator: p.~109, equation~$(*)$. Actual locus: **p109, displayed(*) and following proof via Feferman Theorem2.13**.
Evidence: https://projecteuclid.org/journals/notre-dame-journal-of-formal-logic/volume-30/issue-1/Pathologies-in-two-syntactic-categories-of-partial-maps/10.1305/ndjfl/1093634998.full
The source explicitly constructs an index whose PA-provable domain is any specified Σ1 formula and whose output, when defined, is the input. This is equivalent to V29’s PA-provable graph identity. The subsequent restriction/range argument is proved in V29 itself.

### Montagna — sections/01-introduction.tex:46
Status: **supported**. Cited locator: none. Actual locus: **pp105–108, S/S′ definitions and structure**.
Evidence: https://projecteuclid.org/journals/notre-dame-journal-of-formal-logic/volume-30/issue-1/Pathologies-in-two-syntactic-categories-of-partial-maps/10.1305/ndjfl/1093634998.full
The cited source introduces the unprimed syntactic p-recursion category S based on PA-provable equality. V29 applies its own generalized criterion to that unprimed construction and DPM’s extensions.

### Montagna — sections/01-introduction.tex:126
Status: **supported**. Cited locator: Remark 3.1. Actual locus: **p114, Remark3.1, final two sentences**.
Evidence: https://projecteuclid.org/journals/notre-dame-journal-of-formal-logic/volume-30/issue-1/Pathologies-in-two-syntactic-categories-of-partial-maps/10.1305/ndjfl/1093634998.full
Remark3.1 explicitly concludes effectively inseparable domain pairs exist in S (and claims S′ as well). V29 restricts the attribution to S, so it avoids perpetuating the later-invalidated primed category assertion.

## Heller’s printed errors checked explicitly

At §5 p1260, the printed inverse-image type is DomX→DomY even though its formula φ*ε=dom(εφ), for φ:X→Y, forces DomY→DomX. This was checked visually on the original page. V29 already has correct variance. The same source page repeats C×P in both naturalizer clauses; V29 does not copy that axiom list. Neither source error was silently corrected and then presented as a verbatim source statement. At §6 p1261 the receiving/range agreement law is legible and matches V29.

## Retrieval record and limits

Primary scans and extracted/OCR text reside under `tmp/audit_v29/evidence/recursion/`. Library identities and routes are recorded above and in JSON. Bernardi was unavailable from AMS (403) and its author PDF link returned404, but its author-uploaded primary text contains the exact numbered claims and page breaks read here. ProjectEuclid required a security check for Montagna; the supplied original journal scan resolved access. The Lengyel2004 image scan required OCR; Theorem26 p27 and the relative-case proof were read, not inferred solely from publisher abstract. ArXiv browser opening was disabled, but the public PDF downloaded successfully. Metadata/search snippets were used to locate and corroborate sources, not as substitutes for primary claim verification.

No quotation from these eight sources appears in the reviewed citation uses beyond terminology and titles. The numerical precompleteness definition and all equations are paraphrase/notation translation, with their scope checked above.
