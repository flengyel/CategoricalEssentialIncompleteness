# Mathematical-writing review — version 58

The revised manuscript needs no further writing repair on the source reviewed here. Retain its organization, the abstract's current contribution statement, and the introduction's separation of the general criteria from the three applications. The previously identified local ambiguities and the two optional closing-sentence deletions have been addressed. The reference-audit follow-up and final PDF validation are recorded below; this is not a certification of every proof or external reference.

Source: *Logical consequence and essential incompleteness in recursion categories*, Version 58, 14 November 2026, in `revision-v58/manuscript/latex/`. The report records a fresh reading of the edited manuscript, not just a search of the v57 corrections. Manuscript source anchors are relative to that directory. The manifest has since been synchronized to v58; the manuscript-only checks pass. No manuscript source was edited by this reviewer.

## Current outline and argument

[outline.md](outline.md) records all 14 sections and 53 subsections, their functions, dependencies, and the comparison of each abstract sentence unit and introduction paragraph with the body. The headings and nested inputs were checked before the body reread. The actual order is:

1. Introduction and related work: the computation-first problem, two incompleteness criteria, existence hypotheses, and application scope.
2. Categorical preliminaries: restriction structure, range functors, partial-map categories, and recursion/Turing categories.
3. Diagonal comparison and complementary conditionals: the computational theorem and the condition that yields source inseparability.
4. Internal theories and essential incompleteness: generated theories, soundness comparison, the inseparability criterion, generation reflection, translations, change of ambient category, and the free signed theory.
5. Theory extensions and recursion categories: partial slices, extension functors, and transfer to the constant family.
6. The syntactic recursion category: the PA-provable graph quotient, predicate presentation, and parameterized syntax and deduction.
7. Interpretation and soundness: models, lifted conditionals, standard-code soundness, and ultrapower comparison.
8. Essential incompleteness of arithmetic: internal comparison, a family indexed by axiom enumerations, uniform independent sentences, numerical realization, and associated categories.
9. Miller sequences and essential incompleteness: representation-independent computation, inseparable cuts, field syntax, and associated categories.
10. A recursion category from a three-point space: the fork category, endpoint interpretations, propositional and first-order theories, and associated categories.
11. Appendix A: generic syntax, substitution, initial deduction algebras, and generated images.
12. Appendix B: construction of the cosheaf/fork category and its Turing morphism.
13. Appendix C: the counterexample establishing the need for lifting.
14. Appendix D: the faithful family of model interpretations and its limitations.

The central question is whether categorical axioms for partial computation, supplemented by explicit syntax and deduction hypotheses, produce internal theories for which computational inseparability forces essential incompleteness. The general results precede their realizations. Appendices A and B are explicit forward dependencies, not circular arguments. The numerical realization proves effectiveness facts unavailable from a bare set-level identification; the Miller and fork constructions verify different parameter and naturality conditions. No whole-section reordering is justified.

## Comparison with the front matter

The revised abstract states the constant-family equivalence directly: a consistent theory containing the fixed global logical theorem is essentially incomplete exactly when its constant family in the associated category is essentially incomplete (`abstract.tex:14–16`). This is the content of Theorem 5.3. The family is no longer described as an unspecified “corresponding internal theory,” and no operation is attributed grammatically to the family itself.

The introduction still gives a sufficient combined package of assumptions for the categorical and internal-theory conclusions (`sections/01-introduction.tex:64–81`). The partial-slice Turing structure and categorical extension functor are established in §5.1–5.2 before using the additional syntax hypotheses. This does not make the introduction false, and no replacement paragraph is recommended. The introduction's arithmetic paragraph distinguishes the original arithmetic theories from the separate signed first-order theory used in the associated-category application. Its Miller and cosheaf paragraphs preserve their stated computation and extension conditions.

The abstract and introduction preview familiar concepts appropriately for the intended audience. Adding elementary definitions there would obscure the contribution. Formal definitions and the hypotheses particular to this paper appear in §2, §4, and Appendix A, with explicit references when needed earlier.

## Applied repairs and final findings

| Location (source; PDF page) | Check performed on v58 | Assessment |
|---|---|---|
| `abstract.tex:14–16`; p1 | Compared the revised constant-family equivalence with §5.3 and the final theorem statement. | Resolved. The sentence identifies the construction and preserves consistency and the fixed-logical-theorem hypothesis. |
| `sections/03b-internal-adjunctions.tex:350–353`; p14 | Checked the Boolean valuation's quantifier operation and its subsequent use in the induction. | Resolved. Universal quantification is explicitly the second projection `\pi_2:V\times\Two\to\Two`; a type alone is no longer offered as the operation. |
| `appendices/b-three-point-cosheaves.tex:568–571,595`; p81 | Compared the cited convention and proof with Appendix A's ordered injections and diagonal pullback. | Resolved. Truth is the second injection in both places, and the proof uses the second summand. |
| `sections/04-theory-extensions.tex:242–245`; p17 | Reread the end of §5.3 after deletion of its two general summary sentences. | The substantive numerical-carrier example remains coherent and needs no replacement transition. |
| `sections/01-introduction.tex:153–160`; p3 | Reread the paragraph with the Bernardi locator changed to Sections 2–3. | The prose still identifies the reference's particular contribution and the PA-provable-equality example. Accuracy of the locator is the reference auditor's separate check. |

No additional necessary clarification, optional prose substitution, or section move was established by the full current-source reading. That conclusion does not rest on counting forbidden words. The word searches below were used to locate passages for contextual inspection, not to decide acceptability mechanically.

## Definition order, notation, and terminology

| Notion | Introduction and subsequent use | Verdict |
|---|---|---|
| Composition, restrictions, total morphisms, domains | Composition order and restriction axioms: §2.1, `sections/02-categorical-preliminaries.tex:5–30`; the domain synonym is attributed there. | Defined before the comparison arguments. Retain “domain” where it denotes the restriction idempotent. |
| Restriction order, compatibility, complementary pairs, inseparability | §2.1, lines32–47. | Definitions precede both computational criteria; compatibility is used with the same meaning in the Miller construction. |
| Range functor and coproduct comparison | §2.2, lines132–147; its failure to preserve products is illustrated immediately. | No missing assumption is concealed by the term. The example serves a mathematical distinction and should remain. |
| Restriction splitting, Karoubi envelope, partial maps | §2.1, lines65–102. | Types and distinctions are explicit; completion by all idempotents is not confused with restriction-idempotent splitting. |
| Recursion category and Turing category | §2.3, lines166–190. | Their relation and hypotheses are explicit. Familiar abstract previews do not require duplication of these definitions. |
| Sentence theory and essential incompleteness | §4.1, `sections/03a-internal-theories.tex:11–43`; generated sentence closure in Appendix A. | Theory, derivation object, conclusion morphism, image and restriction idempotent are distinguished. |
| Logical translation | §4.4, `sections/03b-internal-adjunctions.tex:61–93`. | Object and morphism components and rule witnesses are specified. The statement that witnesses are not part of the translation is needed to define its morphisms, not a defensive aside. |
| Constant family and associated category | §5.1 and §5.3, `sections/04-theory-extensions.tex:23–30,166–175`. | Slice objects and the functor `B_U` are typed before the transfer theorem. The revised abstract names this family. |
| Numerical code, representative and equivalence class | §6, `sections/05-syntactic-recursion-category.tex:10–36,48–55,104–121`; §8.4 gives explicit numerical equivalences. | The graph index is distinguished from its denotation and its PA-provable equality class. The primed quotient counterexample is substantive. |
| Syntax, binding and substitution | Appendix A, lines136–154,185–212,274–406; realization §6.3. | Named variables and admissibility are explicit; the paper does not silently substitute alpha-equivalence for literal named-variable syntax. |
| Boolean conventions | Appendix A, lines37–112,136–146; Appendix B, lines568–595. | The two injections and the equality test now agree. Different summand orders in explicitly displayed conditionals remain deliberate. |
| Stable under parameters | Appendix A, lines147–154. | Defined by pullback into slices, with forward references from earlier uses. |
| Frame | §10, `sections/09-three-point-space.tex:109–114`; constructed in Lemma B.6. | The three isomorphisms are specified and Heller is cited. This is a defined technical term. |
| c.e. subfunctor and compatible theory family | §10, lines58–63 and543–549. | Components and transition conditions are defined; neither phrase substitutes for missing construction. |
| Proper theory inclusion | §5.2, `sections/04-theory-extensions.tex:104,143–145`, and §10.9. | Used in the familiar sense of a monomorphism that is not an isomorphism; the proof makes this meaning explicit. No dictionary entry is needed. |

The current TeX was searched for process jargon and uninformative modifiers. “Option-valued,” “failure tag,” “success value,” “source derivation algebra,” “raw,” “actual,” “pipeline,” “checkpoint,” “workflow,” “obviously,” “clearly,” and “robust” are absent from the publication text. Bibliographic titles are excluded from any proposed normalization. The defined `tag_n` map remains legitimate: it encodes a specified coproduct summand in Lemma 6.8, rather than introducing an unexplained programming metaphor.

The inspected occurrences of “canonical” name maps determined by specified product or coproduct data. “Natural” refers to natural transformations, natural isomorphisms, or natural numbers. “Standard” separates external numerical codes from nonstandard-model elements. “Ordinary” in Appendix C distinguishes unrelativized recursion from recursion relative to the halting set. “Retain” describes an actual coordinate or component preserved by a construction. These are not empty modifiers and need no mechanical replacement.

## Economy and proof exposition

The requested economical style is applied by requiring each paragraph to define data, explain a relevant distinction, state a claim, justify an inference, or locate a result. This is an editorial application of the requested Došen–Petrić economy; no quotation or attributed rule from those authors is asserted here.

The removal of the two closing sentences of §5.3 improves the ending without removing its carrier example. Further compression of the following passages is not recommended:

- The two directions of the syntactic/numerical comparison, including computability of the inverse coding maps in §8.4, establish more than a set bijection.
- The derivation-tree induction in Lemma 6.8 identifies a tuple in `B_n(Q,q)` and then its code in the corresponding summand of `H(Q,q)`. This typing is part of the argument.
- The Miller construction separates a representation of the sequence, the oracle program, its common domain and value, and the field interpretation. Those distinctions carry the hypotheses.
- The central-component argument for the fork Turing morphism in Appendix B verifies the exact domain needed for naturality. A phrase such as “the construction is natural” would not replace it.
- The repeated realization pattern across the arithmetic, Miller and fork applications checks different effective, semantic, and parameter conditions. It is not redundant merely because the tree inductions have a common shape.
- Appendix C's counterexample and Appendix D's failure of preservation of the Turing morphism bound the general assertions. They are not defensive commentary to delete.

The related-work paragraphs each state an antecedent, comparison, or motivation. The revised paper does not justify deleting a contextual reference solely because no proof invokes it. New factual corrections to those paragraphs remain subject to the separate source audit.

## Governing source and actual reading scope

The complete supplied Knuth–Larrabee–Roberts *Mathematical Writing* was read in the preceding review, including all 43 sections and handouts. That reading is reused here; this review does **not** claim a second complete manual reading. For v58, Section 1's guidance on theorem statements, complementary explanation, audience knowledge, notation, readable sentences, openings and jargon was reread, together with the definition-placement discussion of §4, Lamport's §32 handout on unnecessary prose, and relevant §37 discussion of terminology and proof order. Printed pages, not PDF image indices, govern the following citations:

- §1.5, p2: self-contained theorem statements, applied with contextual judgment.
- §1.10–13, pp2–3: connected explanation, complementary descriptions, variables introduced at use, and prose that remains readable when formulas are skimmed.
- §1.14 and17, p3: consistent notation and unambiguous left-to-right reading.
- §1.24 and26, pp5–6: direct openings and avoidance of unnecessary jargon.
- §§4–5, pp9 and12: definition placement depends on the reader and context; it is not a compulsory front-loaded dictionary.
- §32, p71: Lamport's concrete deletion of non-contributing introductory and evaluative prose.
- §37, pp90–93: readable subsection transitions, contextual definitions and proof dependencies.

The current review covered all 24 TeX files, including main file, preamble, abstract, bibliography, all section and nested-input files, and all four appendices. The lead reviewer reread the complete source except the Miller application, fork application and Appendix B, which were reread in full by an independent collaborator; the lead checked their reported repair locations and terminology conclusions against the current source. The section and appendix source total was 7,578 lines at the initial v58 reading snapshot and is 7,588 lines after the ten-line expansion of Lemma 6.1; that expanded lemma was reread in full. Search output supplements this full reading rather than replacing it.

### Current check state

- **Checked:** current source organization, every front-matter claim against its corresponding body result, definition and notation order, the applied v57 writing repairs, and the paragraph roles and technical distinctions listed above.
- **PDF check completed:** the final rebuilt PDF has 87 pages and identifies Version 58, 14 November 2026. The revised abstract and projection passage were inspected on pages 1 and 14. After the final rebuild, the complete Lemma 6.1 and its proof were inspected on page 18 and the equality convention and Proposition B.10 on page 81. The additions fit cleanly and the symbols, paragraph order and reference numbers are readable. This is a targeted visual check, not an inspection of every rendered page.
- **Reference/manifest follow-up completed:** the reference audit records all 32 bibliography entries and 66 citation occurrences as covered. Its two corrections are the Bernardi locator and the explicit composition argument in Lemma 6.1, both reread for this report. The final manifest selects v58; no later source change remains pending in this writing review.
- **Outside this writing review:** a fresh Lean build, certification of all proofs, and independent verification of every factual reference claim. Current Lean status must be taken from the synchronized correspondence report rather than inferred from prose changes.

No additional manuscript change is proposed by this report.


## Final follow-up: Lemma 6.1

The whole revised lemma and its context were reread at `sections/05-syntactic-recursion-category.tex:37–120`, especially the added proof at lines84–101 (PDF p18). The sentence defining the fixed index `c` specifies the paired input, simulation order, and intermediate value. The equation `\operatorname{comp}(f,e)=\operatorname{s}(c,\langle f,e\rangle)` agrees with the displayed specialization convention and the composition formula. The two directions are justified by combining and extracting finite halting traces, followed by the stated PA verification. The final sentence explains functionality by determinism. The following paragraph preserves the distinction between an index and its equivalence class and uses the composition formula at the intended place.

This replaces attribution of the exact composition biconditional to a source that did not print it with an explicit argument in the paper. The terminology is conventional, the variables and order are explicit, and no new empty qualifier or unnecessary rhetorical sentence was introduced. No further editorial repair is proposed. This follow-up records the writing check and the argument as presented; it does not substitute for the independent mathematical review or a kernel verification.
