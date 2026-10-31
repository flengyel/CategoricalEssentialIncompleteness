# Mathematical-writing review of the revised appendix

Reviewed source: `/workspace/scratch/9e446291e628/output/appendix/first_order_syntax_and_deductive_closure_appendix.tex`, lines 1–598, titled *Syntax and deductively closed theories*. The standalone source has no separate version designation. This review concerns the revision containing the explicit Boolean copairings and the corrected composite in the substitution proof, read on 31 October 2026. PDF anchors refer to the freshly compiled seven-page standalone PDF supplied by the root reviewer.

The appendix now states the Boolean construction as morphisms and identifies the composite used in the initiality argument correctly. I find no further necessary prose or terminology repair in this pass. Its exposition follows the construction's dependencies. The two optional changes below concern vocabulary only; neither diagnoses a mathematical error or an invented concept.

## 1. Actual outline and dependencies

| Existing subsection | Source / PDF | Function and dependencies |
| --- | --- | --- |
| A.1 Categorical hypotheses and notation | 43–110 / p. 1 | States regularity and the additional coproduct hypotheses; constructs Boolean morphisms; fixes the interpretation of variable notation; specifies decidable equality, signature objects, and parameter stability. |
| A.2 Terms, formulas, and free variables | 112–213 / pp. 2–3 | Defines the syntax endofunctor and its initial algebra; introduces constructors and induction; constructs list operations and free-variable morphisms; defines the sentence object and derived existential quantification. Depends on A.1. |
| A.3 Admissible substitution | 215–350 / pp. 3–4 | Defines the algebra whose initial morphism computes one-variable substitution, then obtains the admissibility subobject by pullback. Explains binding and proves identity and absent-variable substitution. Depends on A.1–A.2. |
| A.4 Inference rules and deductively closed subobjects | 352–431 / p. 5 | Reintroduces the weaker ambient hypotheses, defines the inference endofunctor in a slice, and proves that the image of its initial algebra is the least closed subobject. This construction is independent of the syntax and substitution machinery. |
| A.5 First-order theories | 433–550 / pp. 6–7 | Gives the logical schemes and their parameter objects; applies A.4 to the syntax of A.2–A.3; obtains sentence theories and represents their subobjects as partial identities, with the additional hypothesis for an existing restriction splitting. |
| A.6 Propositional theories | 552–575 / p. 7 | Applies A.4 to the simpler propositional syntax functor. Uses the displayed propositional schemes, but does not import the binding or decidable-equality assumptions. |

The principal construction is the least closed subobject theorem, Theorem A.5 (`thm:least-theorem-subobject`, lines 401–430). Proposition A.3 (`prop:categorical-substitution`, lines 269–293) supplies the substitution needed by the first-order calculus. Theorem A.6 (`thm:first-order-theory`, lines 497–512) applies the general construction and identifies its sentence part. No alternative outline is recommended.

## 2. Verified source comparison

The governing source is Knuth, Larrabee, and Roberts, *Mathematical Writing*, Stanford report, read from the supplied `tmp/review_sources/klr.txt` and its corresponding PDF. Section and printed-page references below refer to that report, whose 117 PDF pages include 115 numbered text pages. The complete report, §§1–43 and its handouts, was read during this review sequence. Its advice is contextual, not a uniform prohibition on technical vocabulary or explanatory prose.

| Current location | Assessment | Verified source principle or independent rationale | Action |
| --- | --- | --- | --- |
| 38–41, p. 1 | The opening states the object being constructed and the machinery it uses. | KLR §1, points 12 and 24: orient the reader and give the opening a clear purpose. | Retain. |
| 57–78, p. 1 | The former phrase “finite coproduct tables” has been replaced by an explicitly typed isomorphism and copairings. The construction can now be followed directly. | KLR §1, points 11 and 26: explain introduced language and avoid unnecessary jargon. The judgment that these particular copairings specify the morphisms is an independent categorical assessment. | The requested clarification is complete. |
| 80–110 and 130–148, pp. 1–2 | The variable convention and parameter stability precede their technical use; the raw syntax object is expressly defined. Binding is assigned to the later free-variable and substitution constructions. | KLR §1, point 11; §§4–5, printed pp. 9 and 12: introduce notation near use, allowing contextual judgment about timing. | Retain. |
| 176–178, p. 2 | “Fold” is established initial-algebra terminology. Here it adds a synonym to an explanation already phrased in algebra morphisms. | Independent audience-sensitive preference, supported generally by KLR §1, point 26; not a claim that the word is illegitimate. | Optional replacement given below. |
| 230–248, p. 3 | “Carrier” is legitimate algebraic language, and the displayed objects and operations supply its meaning. “Objects” would match the categorical presentation more directly. | Independent vocabulary preference. KLR §37, printed pp. 91–92, stresses consistent terminology; it does not forbid “carrier.” | Optional replacement given below. |
| 266–267 and 287–293, pp. 3–4 | The matching-variable explanation identifies why the original body is retained. The proof now explicitly composes the algebra morphism with the projections before invoking initiality. | KLR §1, points 10–11: connect formulas and give complementary explanation. The composite's type is a mathematical issue distinct from prose polish. | Retain both passages. |
| 355–430, p. 5 | The rule data, closure definition, theorem, and proof occur together. “With the rule data above” has a precise nearby referent; repeating the entire setup in the theorem is unnecessary here. | KLR §1, point 5 recommends normally self-contained theorem statements; the surrounding discussion and §§4–5 qualify mechanical demands for repeated definitions. | Retain the local organization and explicit ambient hypotheses. |
| 465–482 and 515–550, pp. 6–7 | Parameter objects and admissibility restrictions are stated rather than hidden in verbal qualifications. Sentence closure and its restriction-idempotent representation are distinguished. | KLR §1, points 11 and 14; the skill's separate requirements concerning typing and preserved hypotheses. | Retain. |

Lamport's handout in KLR §32, printed p. 71, demonstrates removal of self-commentary and repetitive introductory prose. It does not justify deleting the explanations at lines 145–148, 199–200, 266–267, 314–315, or 396–399: these passages tell the reader what the constructed morphisms mean or explain a proof dependency. KLR §43, printed pp. 112–115, further emphasizes judgment and context in applying stylistic rules.

## 3. Definitions, notation, and terminology

- **Boolean operations**: `γ`, `¬₂`, `∧₂`, and `∨₂` are introduced and typed at lines 57–73. The four copairing entries follow the order declared by `γ`. No table or unstated set-level evaluation is needed to identify the maps.
- **Conditional notation and variable notation**: lines 74–84 define the pullback subobjects, conditional construction, and interpretation of displayed variables as projections. Subsequent formulas use these conventions. These conventions are substantive and should remain.
- **Decidable equality**: lines 86–98 give the pullback square and its complement. The phrase has an explicit categorical meaning here.
- **Stable under parameters**: lines 104–110 define the slice construction and universal property before Definition A.1 uses them. The introductory “parameterized initial algebras” is a harmless preview of this explained notion.
- **Raw named-variable syntax object**: lines 130–133 define it by initiality. Lines 145–148 explain the role of the variable and quantifier constructors. This is declared local terminology with a mathematical purpose, not undefined jargon.
- **Free-variable occurrences**: the maps are defined at lines 185–198; lines 199–200 specify that their list values retain repetitions. This distinction is necessary because a list object is being used rather than a finite-subset object.
- **Sentence object**: lines 202–210 define it by pullback. Its later reuse as `S` in the first-order section is unambiguous. The propositional section explicitly starts a new setup at lines 555–558.
- **Failure, success, and result components**: lines 220–228 define the coproduct and lifted morphisms; lines 232–248 give the paired objects and explain both components. “Return,” “branch,” and “result” are useful descriptions of the specified morphisms. They are not substitutes for missing definitions here.
- **Admissibility and substitution**: the pullback at lines 275–282 defines the domain and substitution morphism before the notation `φ[x:=t]` is adopted at lines 317–318. The phrase “absent variable” at lines 330–336 is immediately expressed by the displayed subobjects.
- **Rule instances and deductive closure**: lines 360–385 supply the morphisms and inference endofunctor; lines 387–399 define closure and explain uniqueness. All terminology has a specified categorical referent.
- **Sentence theory**: lines 515–517 explicitly define the stronger sentence-level closure condition before leastness and monotonicity are asserted.
- **Partial-map representation**: lines 528–536 state the span construction and explain the range partial identity; lines 537–547 define the restriction-splitting notation and state the additional partial-inverse equations. The final representation is conditional on those equations, as it should be.

I found no remaining phrase comparable to “finite coproduct tables”: a putative construction named without its actual meaning. A term's computational associations do not by themselves make the categorical construction informal. In particular, neither “fold” nor “carrier” is an invented term.

## 4. Prioritized recommendations

**Necessary changes identified in this writing pass: none.** Preserve the revised Boolean formulas, the corrected projection composite, the mathematical explanations, the differing ambient hypotheses, and all four references.

Two optional local simplifications are available if the editor wants the exposition to use only the algebraic vocabulary already introduced:

1. At lines 177–178, replace “These are the algebra-morphism equations of the corresponding folds.” with:

   > These are the algebra-morphism equations supplied by list initiality in the corresponding slices.

2. At line 230, replace “In `$(\mathcal D/E)^2$`, use the carriers” with:

   > In `$(\mathcal D/E)^2$`, use the objects

These should not trigger a wider terminology rewrite. There is no justification in this pass for changing “raw named-variable syntax,” deleting the explanatory treatment of binding, adding an unrelated literature survey, or moving the numerical realizations back into the appendix.

## 5. Scope and checks

I re-read the complete revised standalone source, lines 1–598, including its bibliography. I used text extracted from the fresh seven-page PDF to confirm the page locations above and the presence of both substantive revisions. I read the complete mathematical-writing skill and its terminology and source-review references earlier in this review sequence and applied them here. I also completed the full KLR report reading earlier in this sequence; the specific advice cited above was checked in its actual text.

This is a source-based mathematical-writing review of the appendix, not a new certification of the other manuscript sections or all mathematical claims. I did not reverify the four mathematical bibliography sources in this pass, modify manuscript files, compile independently, or perform a fresh visual page-layout audit. The root reviewer is handling the final build and rendering checks.
