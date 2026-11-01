# Cockett 1990 overlap report: Version 30 main paper

The attached paper establishes the parameterized list structure that Appendix A uses and §5 realizes. The current manuscript already attributes that structure to Cockett. The attached paper does not, by itself, replace the many-sorted syntax, dependent derivation-tree, regular-image closure, substitution-realization, or numerical comparison proofs. This is a finding about this verified source, not a claim that those constructions are original in the wider literature.

Scope: `Logical consequence and essential incompleteness in recursion categories`, Version 30, 1 November 2026; main manuscript only. Read the complete Appendix A, §5a (`05a-internal-syntax.tex`), the syntax/list/derivation portion and comparison in §7.4 (`08c-numerical-realization.tex`), and the relevant introduction. Source: the supplied `upload/cockettListarithmeticDistributiveCategories1990.pdf`, Journal of Pure and Applied Algebra 66 (1990), 1–29. The extraction was searched throughout; relevant primary PDF pages 7, 9, 16–18 were also rendered and read. Printed page numbers coincide with PDF page positions. The full article was not subjected to an independent correctness audit.

## (A) Kill-shots / hard blockers

No duplication-based mathematical blocker is established. In particular, no checked passage claims that parameterized lists are new, and Appendix A lines 155–157 expressly attributes parameterized list recursion to Cockett. The introduction's description of realizations (lines 58–62) is an assertion about the concrete category and its equality of morphisms, not a claim to invent list recursion.

The following negative conclusion is decisive for the proposed compression: Cockett's Theorem 5.5 is a theorem about a linear domain equation `R ≅ B + A×R`, subject to a tail-contraction condition, in an arithmetic distributive category. It cannot be substituted verbatim for the initiality of the nonlinear, two-sorted syntax functor `K` or the premise-compatible derivation endofunctor `H`. Deleting their realization proofs on this citation alone would leave actual hypotheses/conclusions unproved.

## (B) Major weaknesses

No current major defect is established by this source comparison. There are, however, two precise ways a source-based rewrite could create a major defect.

**B1. Treating abstract list initiality as realization of the selected syntax and derivation codes.**

- Anchor: Proposition 5.5, p.16, `05a-internal-syntax.tex` lines 372–471; Proposition 5.7, p.18, lines 513–618; Lemma 5.8, p.19, lines 637–806; Proposition 7.8, p.38, `08c-numerical-realization.tex` lines 281–474; numerical/syntactic derivation comparison lines 498–569.
- Claim as written: the chosen carrier formulas are Σ₁, the displayed evaluation relations define morphisms, and the universal equations and uniqueness are proved in `T`; the numerical instance uses computable functions on the specified carriers.
- Potential failure mode if removed: `unproved` / `misuse_of_prior_work`.
- Evidence: `structural_argument` and `citation`. The `K`-functor includes nonlinear terms `X^k`, `X²`, `Y²`; the `H`-functor includes compatibility pullbacks `R_n×_{F^n}Q^n`. Cockett's Theorem 5.5, p.17, has neither form. The introduction, p.2, says the broad assertion about all internally specified free algebraic constructions is beyond this paper's scope. Section 6, p.27, explicitly distinguishes its connected-limit result from transferring initiality results without modification.
- Downstream impact: removing these obligations would break Theorem 5.9 and subsequent identifications of actual proof codes, images, and ranges. A generic existence theorem does not identify a chosen program's graph with a categorical fold.
- Repairability: preserve the existing proofs, or cite a separately verified theorem and explicitly discharge its stronger, correctly typed instance hypotheses and code-identification requirements. This source alone does not provide that replacement.

**B2. Equating Cockett's least subsemirecursive with the least rule-closed regular image.**

- Anchor: Theorem A.5, p.61, appendix lines 471–501; Definitions/rule data lines 422–459.
- Claim as written: for a finite rule presentation on arbitrary `F`, assuming an initial algebra in `D/F`, the regular image of its conclusion is the least rule-closed subobject.
- Potential failure mode if replaced by Cockett Proposition 5.3: `misuse_of_prior_work` / `unsupported_generalization`.
- Evidence: `citation` and `structural_argument`. Proposition 5.3, p.16 (proof p.17), starts from an isomorphism `R≅B+A×R` and constructs the least subsemirecursive that is prerecursive. Theorem A.5 assumes regularity and existence of an initial rule algebra; it does not assume arithmetic, a contraction, or stable disjoint coproducts. Cockett explicitly removes regularity, p.3. A.5 can use rule compatibility constraints and arbitrary arity, unlike the fixed linear action of Proposition 5.3.
- Downstream impact: a bare replacement citation would not establish that images of general logical derivations are closed under the inference rules.
- Repairability: keep A.5 with its existing generic-factorization attribution; distinguish the thematic least-generated-subobject resemblance from identical statements. No current fatal flaw is asserted.

### Current outline and its mathematical functions

The reviewed portion has a coherent dependency order:

1. Appendix A.1 fixes regularity, coproducts, Boolean tests, equality, and stability under constant parameters.
2. A.2 assumes initial syntax and list algebras, constructs free-variable lists and the sentence pullback.
3. A.3 constructs the option-valued substitution fold and its successful-domain pullback.
4. A.4 specifies finite inference rules in `D/F` and transfers an initial derivation algebra to its regular image.
5. A.5 specifies the first-order rule system, obtains least formula/sentence theories, then compares regular images with split ranges.
6. A.6 gives the propositional specialization.
7. §5.1 presents `B_T` through Σ₁ predicates and `T`-provable graph equality, proves regularity and stable disjoint coproducts.
8. §5.2 constructs the actual syntax and list codes and proves initiality in every constant-parameter slice.
9. §5.3 identifies the selected numerical free-variable/substitution algorithms with the Appendix A folds.
10. §5.4 constructs derivation codes for arbitrary finite rule data and applies Appendix A to obtain the generated theory.
11. §7.4 repeats the required realization in the extensional numerical category and compares concrete derivation carriers with the syntactic ones.

No revised outline is needed for the Cockett attribution alone. In particular, moving a generic theorem citation in front of the instance construction must not erase the construction on which later comparisons depend.

## (C) Minor issues

**C1. The existing Cockett citation can be more exact.**

- Anchor: appendix lines 148–157, especially 155–157.
- Claim as written: for list objects the parameter-stable initiality property is the parameterized recursion property studied by Cockett.
- Status: verified. Failure mode: none; optional positioning refinement only.
- Evidence: `citation`. Cockett Lemma 2.2 and Definition 2.3, printed p.7, identify parameterization with preservation of recursion by `I_P:D→D/P`; Definition 2.4(ii), p.7, names the all-object list-arithmetic structure.
- Suggested replacement: `For list objects, this is Cockett's parameterized recursion property~\cite[Definition 2.3 and the discussion following it]{CockettLists}.`
- Editorial rationale: make the role of the source explicit and attach it to the specific shared definition. KLR §1 point 11 supports explaining a definition in a complementary way; §1 points 10 and 13 support maintaining connected prose around formulas. These are verified writing principles, not claims that KLR mandates this particular citation.

**C2. Identify the list realization as an instance when helpful.**

- Anchor: Proposition 5.6, p.17, lines 473–504.
- Status: no false novelty claim found. An optional one-sentence introduction could say: `The coded finite sequences realize parameterized list recursion in \(\mathcal B_T\).`
- Evidence: `citation` plus the typed derivation below.
- Recommended action: keep the current short proof unless an actual length reduction is demonstrated. The Cockett-based route needs an arithmetic-category setup that the manuscript currently does not state as an independent preliminary result.

### Concise typed comparison

Use the manuscript convention throughout: `g f = g∘f`, first `f`, then `g`. Cockett uses diagrammatic right composition, so his `f.g` must be reversed when imported.

- Cockett's action category `Act_A(D)` has objects `g:A×X→X` and morphisms `h:X→Y` with `h g = g'(1_A×h)`. The forgetful functor `U_A:Act_A(D)→D` is covariant.
- `rec(A,B)` carries `r_0:B→R` and `r_1:A×R→R`. For any `b:B→X` and `g:A×X→X`, the fold `a:R→X` has equations `a r_0=b` and `a r_1=g(1_A×a)`. This is the correctly typed manuscript version of the universal property on Cockett p.6 and Lemma 5.6's statement on p.18.
- `I_P:D→D/P` is covariant, with `I_P(X)=(X×P→P)` and `I_P(h)=h×1_P`. Parameterization is preservation of recursive objects by this functor (Definition 2.3). In the list case, the initial carrier in the slice is `P×W→P` for `1_P+(P×V)×_P(-)`.
- The two formulations are equivalent at the level used here. Parameterized lists give `rec(V,B)≅W×B` by folding in `D/B` into `B×X→B`; conversely free `V`-actions on arbitrary seeds `B` give the slice fold for `X→P`, and composing the fold with `X→P` shows that it lies over `P` by uniqueness. Thus the common parameter notion is substantive, not merely shared vocabulary.
- A semirecursive consists of `split:R→B+A×R` inverse to `[r_0,r_1]:B+A×R→R` (Definition 5.1, pp.15–16). In manuscript order the equations are `split r_0=ι_0`, `split r_1=ι_1`, `[r_0,r_1] split=1_R`.
- Its tail/shrink is `t=[r_0,π_R] split:R→R`, where `π_R:A×R→R`. Cockett's displayed `split.(r_0; p_1)` has this type; it is not `split∘[r_0,π_R]`.
- A contraction has `β:R→N` satisfying `t^{β(r)}(r)=t^{β(r)}(t(r))` (Definition 3.1, p.9). A prerecursive has that contraction with fixed subobject `r_0:B↪R`.
- On our coded lists, `t(nil)=nil`, `t(cons(v,w))=w`, and `β=len:W→N`. The equation follows because both sides are nil after `len(w)` steps. In the slice the tail retains the parameter `p` and the fixed subobject is the nil section `P→P×W`. Theorem 5.5 then yields recursive initiality **once the arithmetic/distributive hypotheses are established there**.

### Hypothesis comparison

| Result | Ambient assumptions | Input algebraic object | Output |
|---|---|---|---|
| Cockett Theorem 5.5 | Arithmetic distributive category: finite limits, stable disjoint finite coproducts, parameterized NNO | `R≅B+A×R` whose shrink is a contraction with fixed subobject `B` | `R` is the free `A`-action generated by `B` |
| Cockett Proposition 5.3 | Same arithmetic distributive background | Any `R≅B+A×R` | A least subsemirecursive that is prerecursive |
| Appendix Theorem A.5 | Regular category with finite coproducts | Assumed initial `H`-algebra in `D/F`, for finite rule data `R_n→F^n` and `R_n→F` | Its conclusion image is least rule-closed subobject |
| Appendix Definition A.1 | Regular category, stable disjoint finite coproducts, decidable equality on chosen `V` | Assumed parameter-stable initial `K` and chosen `List(V)` | Syntax structures to be used in subsequent folds |
| Proposition 5.6 | The specific category `B_T`, built from Σ₁ formulas modulo `T`-provable graph equality | Explicit coded lists on arbitrary chosen `V` | A Σ₁ carrier and parameter-stable initial list algebra |

The general hypotheses are not simply nested: A.5 uses regular images but no NNO; Cockett's core list theorem uses arithmetic and disjoint stable sums but no regularity. Appendix A assumes selected initial algebras rather than that the whole category is list-arithmetic. Conversely, once Lemma 5.3 and Proposition 5.6 have been proved for every `V`, `B_T` has the structure of a regular locos in the sense relevant here. That is a consequence of the concrete realization, not a free input to it.

## (D) Cross-section consistency failures

No current cross-section inconsistency is established. The following distinctions must survive a source-based revision:

1. **Constant-parameter stability versus full slice locality.** Cockett Definition 2.3/Lemma 2.2, p.7, corresponds to the manuscript's constant objects pulled into slices. Cockett Proposition 6.7, p.28, constructs recursion for arbitrary slice coefficients `f:A→P`; it is broader. Proposition 5.6 does not reprove all of 6.7 merely by treating `P×V→P`.
2. **Forward closure versus separator closure.** In Cockett §4, p.13–15, an `f`-separator is both closed and dividing: `f⁻¹(H)=H`. Appendix A's rule-closed subobjects need only carry the forward algebra structure. Their equality is not definitional.
3. **Split images versus regular images and ranges.** Cockett Lemma 3.2, p.9, concerns the idempotent collapse `c(r)=t^{β(r)}(r)` and its fixed subobject. The regular-image/range comparison of Lemma A.7, p.63, concerns arbitrary total maps in a split restriction category, requires regularity, and separately requires a partial inverse for the monic image. No result in the attached article replaces those hypotheses.
4. **Categorical existence versus equality of selected codes.** §5 uses universal `T`-provable graph equivalence; §7.4 uses extensional equality of partial recursive functions and actual computable relabelings of rule trees. Cockett p.7 itself distinguishes formal primitive-recursive morphisms from equality determined by elements. A citation to an abstract initial object does not identify these two categories' chosen carriers or programs.

There is a limited shared special case worth recording without claiming a generalization. In a common setting with the necessary regularity and a recursive object, take `F=R`, `R_0=B`, `q_0=r_0`, `R_1=A×R`, `p_1=π_R`, `q_1=r_1`. Then Appendix A's rule endofunctor is `B+A×(-)` over `R`, and the conclusion is the fold `rec(A,B)→R`. Its image is the least forward-closed subobject containing `B`. Additional use of the semirecursive isomorphism and image stability relates this image to Cockett's generated subsemirecursive. This is a derived common instance, not an equality of the two printed theorems, and Cockett obtains his result without the regularity assumed by this route.

## (E) Acceptance conditions, non-negotiable

No major reconstruction of the current manuscript is demanded by the attached source. For any proposed compression, these are the verifiable conditions:

1. Keep an explicit Cockett attribution at the definition of parameterized lists; endpoint: an exact Def.2.3/p.7 citation or equivalent precise attribution. Failure is a positioning defect, not a refutation of the mathematics.
2. If replacing Proposition 5.6 by Theorem 5.5, state/prove the ambient arithmetic/distributive assumptions without circularly using the all-object list theorem being replaced, and exhibit the typed nil/cons inverse, tail, fixed subobject, and length bound, including parameters. Endpoint: a complete instance proof. Without it the replacement leaves Proposition5.6 unproved.
3. Retain or replace with verified applicable theorems the many-sorted syntax and dependent derivation-algebra existence/initiality proofs. Endpoint: the precise `K` and `H` of the manuscript have their stated initial algebras. Cockett 1990 alone does not meet this endpoint.
4. Retain the graph/carrier preservation, constructor equations, and equality statements needed to identify the selected free-variable/substitution algorithms and proof-code comparisons. Endpoint: later references to the chosen codes remain justified. An abstract existence citation alone is insufficient.
5. Keep the regular-image factorization argument or an applicable verified citation for A.5, separately from Cockett Proposition5.3. Endpoint: closure of the image under all rules, plus leastness, under A.5's actual hypotheses. Confusing the statements would create a major source-use defect.

## (F) Not checked / uncertainty log

- The separate first-order-syntax note was not reviewed, per scope.
- No whole-paper correctness or novelty verdict is given. The central section-lifting/inseparability theorem was not independently rechecked here; Cockett's connected-limit/locality results do not establish an identity with it.
- The broader “fundamental theorem of data structures” mentioned on Cockett p.2 is explicitly not proved in this paper. Its later literature, hypotheses, and application to this exact `K`/`H` remain unverified in this task. Thus “not established in this source” must not become “new”.
- The current manuscript's Wißmann, Maietti, Aczel, binding-syntax, range-category, and arithmetic-coding citations were not independently source-checked here. Their presence was recorded, not certified.
- No manuscript files were edited or compiled. Existing `main.aux` supplied the current result numbers/pages. Rendered PDF source pages were used to check critical mathematical notation.
- A source-side caution, separate from duplication: Cockett Lemma5.6's **statement** on p.18 correctly uses the target action `g:A×X→X` in `(i_A×a).g=r_1.a` (the extraction can misread `g`). It has an `f`/`b` seed-name typo. In its proof, the displayed chain prints `r_1` where the typed target action should be `g`, and the next sentence cancels that action using “as r_1 is monic”; arbitrary `g` was not assumed monic. This identifies a proof/transcription issue to keep separate; it does not refute the uniqueness statement or Theorem5.5. In particular it supplies no reason to delete our direct uniqueness arguments. An independent repair or full audit of Cockett's proof was not undertaken.

Strongest confirmed blocker: none in the current manuscript from this comparison. Strongest suspected unconfirmed blocker: none asserted; the exact broader data-structure theorem that might shorten the nonlinear/dependent initiality proofs remains unverified. Most important unchecked item: a verified general data-structure theorem with the precise hypotheses needed by the manuscript's chosen `K` and `H`, and its compatibility with `T`-provable graph equality. The conclusions above do not depend on unavailable material; a claim of originality would. Final recommendation: **unknown** as a whole-paper journal assessment; for the requested duplication decision, retain the concrete realizations and sharpen the list attribution if desired.
