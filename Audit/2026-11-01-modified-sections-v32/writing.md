# Scoped mathematical-writing review: Version 32

**Diagnosis.** The four revised passages in *Logical consequence and essential incompleteness in recursion categories*, Version 32 (1 November 2026), introduce the needed terminology before its use and preserve the distinction between the recursion category \(S_T\), its restriction splitting, its total subcategory, and the numerical category. I found no required prose repair in these passages. The two suggestions below are optional improvements in local explicitness. No manuscript edits were made.

## Actual outline and paragraph functions

This is an outline of the existing exposition relevant to the changes, not a proposed reorganization. The local question is how the syntactic partial-map construction supplies a Turing category and how its syntax operations yield the numerical realization used for deductive closure.

| Existing unit | Actual function and dependency |
| --- | --- |
| §2.1, Partial maps and restriction idempotents | Defines restrictions, totality, restriction functors/equivalences, orders, ranges, and restriction splitting. These supply the notation and ambient constructions used in §5.1. |
| §2.2, Products, coproducts, and local connectedness | Defines restriction products, coproducts, and the other categorical structure. Binary restriction products precede the new cartesian definition. |
| §2.3, Recursion categories | Defines prodominical and isotypical categories, then Turing morphisms and recursion categories. The added final paragraph defines a restriction terminal object, a cartesian restriction category, and a Turing category, in that order, and attributes the last characterization to Cockett–Hofstra. |
| §5.1, The total restriction splitting | Introduces \(\mathcal B_T=\operatorname{Tot}(\operatorname{Split}(S_T))\); defines the predicate presentation \(\mathcal P_T\); proves functional search and the equivalence \(\mathcal P_T\simeq\mathcal B_T\); constructs finite limits, regular images, coproducts, and partial inverses; then obtains \(\operatorname{Par}(\mathcal B_T,\operatorname{Mono})\simeq\operatorname{Split}(S_T)\). The new unnumbered paragraph proves that the splitting is a Turing category. The following paragraph extends ranges. |
| §7.4, The numerical realization | Defines \(\mathrm{Rec}\), \(\mathcal C_{\mathrm{rec}}\), tuple codings, and their comparison functors; proves regularity and the partial-map equivalence; constructs syntax/list initial algebras, including parameterized initiality; the revised paragraph identifies the free-variable and substitution algorithms with the categorical folds; the remaining argument constructs derivations and compares the numerical and syntactic conclusion morphisms. |
| Appendix A.1, Categorical hypotheses and notation | Fixes \(\mathcal D\), its limits/coproducts, notation, Boolean operations, conditionals, and variable/signature objects. The revised final paragraph defines stability under parameters, identifies the list case with Cockett's parameterized recursion, supplies exact source locators, and gives the author-requested qualification concerning the printed uniqueness argument. |

Within the modified §5.1 paragraph, the sentences have distinct proof functions: state the claim and Turing object; supply the terminal object; give the product; give the object retractions; identify the relevant source argument; type the original and split morphisms; obtain and restrict the total parameter; calculate the universal factorization; apply the recognition criterion. Within the modified §7.4 paragraph, the functions are: identify the existing algorithms; type their numerical realizations; transfer PA-proved equations to \(\mathbb N\); apply fold uniqueness; construct the admissibility pullback and induced substitution; define the sentence subobject. None is merely a retrospective proof checklist.

## Source comparison and findings

I read the full mathematical-writing skill and both supplementary references, then consulted the supplied KLR *Mathematical Writing* directly: §1, printed pp. 1–6 (PDF pp. 3–8), and §§4–5, printed pp. 9–13 (PDF pp. 11–15). In particular, §1 points 5, 9–15, 17, 23, and 26 cover self-contained claims, complementary exposition, first introductions of variables, notation, sentence parsing, displays, and jargon. §4, printed p. 9, expressly treats definition placement as contextual; §5, printed p. 12, asks that symbols be defined before or very near use. The requirement to write an outline and paragraph-function audit comes from the skill, not from KLR.

| Manuscript anchor | Actual finding | Verified principle or independent rationale | Recommended action |
| --- | --- | --- | --- |
| §2.3, `02-categorical-preliminaries.tex:167–177`, PDF p. 5 | Definitions occur in usable order. The surrounding discussion already establishes that the ambient structure is a restriction category; \(!_X\) and the arbitrary \(f\) have explicit endpoints. | KLR §1 point 11; §§4–5 on contextual definition placement. Repeating the ambient category's name is an independent preference for local explicitness. | Retain. Optionally begin, “In a restriction category \(\mathcal C\), a restriction terminal object \(1\) has …”. This is not a missing-category defect. |
| §5.1, `05a-internal-syntax.tex:270–292`, PDF p. 15 | The unnumbered claim is immediately proved. The proof distinguishes the original representative in \(S_T\) from its split morphism and checks totality of \(re\). “Indeed” introduces mathematics rather than reassurance. | KLR §1 points 5, 10–11, 13; supplementary typing convention. | Retain the claim, proof, and source references. Optionally type the two retraction morphisms, as below. No theorem environment or new diagram is required. |
| §7.4, `08c-numerical-realization.tex:394–413`, PDF p. 39 | The consolidation retains both carrier preservation and constructor equations, the PA-to-\(\mathbb N\) step, fold uniqueness, and the admissibility/sentence subobjects. The four displayed morphisms name their ambient category. | KLR §1 points 10–11, 13–14. The shared codes give a substantive reason for the cross-reference. | Retain. The repeated “same codes” is minor emphasis, not a required cut. Do not shorten the paragraph by removing the transfer or uniqueness step. |
| Appendix A.1, `a-syntax-and-theories.tex:148–160`, PDF p. 57 | The parameterized property is defined before the list-source comparison. Cockett's Lemma 2.2 and Definition 2.3 are the relevant exact locators. The footnote identifies a distinct printed argument and says precisely which cited results are unaffected. | KLR §1 points 11 and 17; independent source-verification and author-authorization considerations. | Retain the citation and the requested footnote. This is a scholarly qualification about published mathematics, not narration of this manuscript's editing process. |

## Definition-order, typing, and notation audit

- **Composition:** \(gf=g\circ f\), with \(f\) applied first, is fixed at §2.1 line 5. The new proof follows it.
- **Restriction terminal object and cartesian:** defined at §2.3 lines 167–171 before the §5.1 claim. In \(!_Yf=!_X\bar f\), both sides have type \(X\rightharpoonup1\). The adjective “cartesian” modifies a restriction category; it does not assert ordinary categorical products of all partial morphisms.
- **Turing morphism/category/object:** the universal factorization with a total parameter is defined at §2.3 lines 156–162. The new Turing-category characterization at lines 172–177 includes the retraction data and cartesian hypothesis. In §5.1 the Turing object is explicitly \(U=(\omega,1_\omega)\), an object of the splitting.
- **Splitting and total subcategory:** §2.1 gives split objects, their morphisms, identity \(e\), and totality condition \(\bar f=e\). §5.1 defines \(\mathcal B_T\) before using it. Consequently “both morphisms represented by \(e\)” is well determined: one has source \((X,e)\), hence is total, whereas the reverse morphism may be partial. Writing those types would help a reader scanning for totality, but does not repair a mathematical omission.
- **Universal computation in the proof:** the representative has type \(X\times\omega\rightharpoonup\omega\) in \(S_T\); \(r:X\to\omega\) is total there; \(re:(X,e)\to U\) is total in the splitting since its restriction is \(e\). The displayed compositions are composable. The reuse of \(f\) for its representative is expressly declared, and therefore unambiguous.
- **Numerical folds:** \(V,\mathrm{Tm},\mathrm{Fm},W\), \(w_0\), and parameterized initiality are introduced before the revised paragraph. The displayed maps belong to \(\mathcal C_{\mathrm{rec}}\). The injection \(\mathrm{Fm}\hookrightarrow1+\mathrm{Fm}\) defines the success summand; its inverse image under \(b_F\) yields \(\mathrm{Adm}\), followed by the typed induced map \(a_F\). The sentence-object inclusion is then typed into \(\mathrm{Fm}\).
- **Parameter categories:** Appendix A.1 fixes \(\mathcal D\) first; \(\mathcal D^r\), \((\mathcal D/P)^r\), and \(P\times X\to P\) identify the ambient categories and the slice constants. No modified construction silently changes ambient category.

I found no invented terminology, unwarranted evaluative adjective, formula-only proof, process narration, or solely defensive paragraph in the modified passages. In particular, the requested Cockett footnote should not be removed under an editorial-process prohibition.

## Prioritized edits

**Required:** none from this scoped prose review.

**Optional 1 — make the terminal definition locally explicit** (`02-categorical-preliminaries.tex:167`):

```latex
In a restriction category $\mathcal C$, a \emph{restriction terminal object}
$1$ has a unique total morphism $!_X:X\to1$ for each object $X$,
satisfying $!_Yf=!_X\bar f$ for every $f:X\rightharpoonup Y$.
```

**Optional 2 — display the direction and totality of the object retraction** (`05a-internal-syntax.tex:276–277`):

```latex
For every object $(X,e)$, the total morphism
$e:(X,e)\to(X,1_X)$ has retraction
$e:(X,1_X)\rightharpoonup(X,e)$, and $(X,1_X)\cong U$
by the coding isomorphism.
```

These are optional clarifications of information already determined by the definitions. No revised outline is warranted.

## Source checks and scope

The supplied primary sources support the new locators: Cockett–Hofstra, *Introduction to Turing categories*, Theorem 3.4, printed p. 189 (PDF p. 7), and §3.5, printed p. 195 (PDF p. 13); Cockett, *List-arithmetic distributive categories: Locoi*, Lemma 2.2 and Definition 2.3, printed/PDF p. 7, and Lemma 5.6, printed/PDF p. 18. I read the adjacent arguments. Cockett–Hofstra §3.5 starts with an already cartesian Turing category; the manuscript appropriately cites its **argument** and independently supplies a terminal object and the total-parameter calculation for \(\operatorname{Split}(S_T)\). It does not need to assert that \(S_T\) itself meets that stronger hypothesis. The Cockett footnote concerns the uniqueness proof of the later Lemma 5.6; Lemma 2.2 and Definition 2.3 neither invoke that argument nor require Theorem 5.5.

I read §2, §5.1, §7.4, and Appendix A.1 continuously, plus the directly used syntactic-category coding/Turing construction, list/substitution realization propositions, and the appendix's categorical syntax/substitution definitions and proof. I inspected the rendered revised passages on manuscript PDF pp. 5, 15, 39, and 57; the displays, references, and footnote are legible and unclipped. No compilation was run by this reviewer. Unchanged surrounding material was consulted for dependencies, not subjected to a new whole-paper review. This report is an editorial assessment of the stated modifications, not mathematical or novelty certification. The Maietti source was not independently rechecked in this writing pass.
