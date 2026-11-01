# Review of modified sections: version 32

The hostile-referee review and the mathematical-writing review found no required correction in the four modified passages. A separate reconciliation checked their findings against the frozen source and the cited primary texts. No manuscript edit is required on the evidence of these reviews. Version 32 remains current.

The paper is *Logical consequence and essential incompleteness in recursion categories*, version 32, 1 November 2026, repository commit `f5041d636916af1e2db9d6494767a81c6a12a1ec`. This is an author-side AI review of the changes in versions 31–32, not a whole-paper review or a claim of formal verification.

## Scope and conclusions

| Passage | Mathematical function | Review conclusion |
| --- | --- | --- |
| §2.3, p. 5 | Defines restriction terminal objects, cartesian restriction categories, and Turing categories. | The morphisms and equations are well typed, and the definitions precede their use. The Turing-category characterization matches Cockett–Hofstra, Theorem 3.4, p. 189. |
| §5.1, p. 15 | Identifies the restriction splitting of the syntactic recursion category as a Turing category. | The partial-map equivalence supplies the restriction terminal object; split products, retractions into the Turing object, and the total parameter establish the recognition criterion. The argument does not assume a terminal object in the original category. |
| §7.4, p. 39 | Uses the existing PA proof of the substitution equations instead of repeating it. | Proposition 5.7 supplies the equations for the same codes. Their interpretation in the standard natural numbers and the independently proved numerical fold uniqueness justify the identification. The admissibility pullback, substitution type, and sentence carrier remain present. |
| Appendix A.1, p. 57 | Attributes parameterized list recursion and qualifies the separate printed uniqueness argument. | Lemma 2.2 and Definition 2.3 on Cockett's p. 7 support the attribution. The requested footnote accurately separates those items from the gap in the printed proof of Lemma 5.6 on p. 18. |

## Disposition

No confirmed mathematical blocker, required prose repair, invented term, or editorial-process paragraph was found in the changed passages. The writing review offers two optional clarifications: explicitly name the ambient restriction category in the terminal-object definition, and display the directions of the two morphisms represented by a split idempotent. Their types are already determined by the surrounding definitions. Neither suggestion changes a hypothesis or repairs a faulty inference. No optional edit has been applied.

The mathematical-writing review consulted Knuth, Larrabee, and Roberts, *Mathematical Writing*, §1 and §§4–5. The reviewers inspected the modified rendered pages 5, 15, 39, and 57. They verified the relevant Cockett–Hofstra and Cockett primary-source passages. Maietti's unchanged citation and the remaining paper were not re-audited in this pass. Existing version 32 build logs are clean; the source was not rebuilt merely to record this review. No Lean code was changed or checked.

There is no concrete unresolved finding in these four changes that requires another revision-and-review cycle. The detailed independent reports follow.


---

# Hostile-referee report

(A) Kill-shots / hard blockers

None confirmed in the four reviewed changes of *Logical consequence and essential incompleteness in recursion categories*, Version 32. This is an author-side audit of correctness, typing, self-containedness, and claim-bearing citations. It is not a whole-paper assessment. No counterexample or invalid inference was exhibited in the changed passages.

(B) Major weaknesses

None confirmed within scope. In particular, the proof that \(\operatorname{Split}(S_T)\) is a Turing category does not assume that the original, terminal-free \(S_T\) is already a Turing category.

(C) Minor issues

None substantiated in the modified passages. The Appendix A.1 footnote states a verified defect in a cited source's printed proof, not the falsity of its lemma.

(D) Cross-section consistency failures

None confirmed. The following checks support that conclusion.

1. **Section 2, p. 5, final paragraph: restriction terminal objects and the recognition criterion.** The equation \(!_Yf=!_X\bar f\) has type \(X\rightharpoonup1\) for every \(f:X\rightharpoonup Y\). The definition requires a unique total \(!_X:X\to1\), and binary restriction products are defined earlier. For every object \(X\), the Turing-object criterion specifies total \(m_X:X\to U\), partial \(r_X:U\rightharpoonup X\), and \(r_Xm_X=1_X\). Its Turing morphism requires, for every object \(Z\) and every \(f:Z\times U\rightharpoonup U\), a total \(r:Z\to U\) with \(f=\tau(r\times1_U)\). These are the hypotheses of Cockett–Hofstra, Theorem 3.4, printed p. 189, read with their preceding definitions. Their proof constructs all \(U\times X\rightharpoonup Y\) universal applications by the displayed retracts. **Evidence: citation and structural_argument; status: verified.**

2. **Section 5.1, p. 15; `05a-internal-syntax.tex:258–292`: the category and the parameter maps.** The dependencies distinguish \(\mathcal B_T=\operatorname{Tot}(\operatorname{Split}(S_T))\) from the partial-map category. The covariant functor \(\mathcal P_T\to\mathcal B_T\) sends a carrier predicate \(C\) to \((\omega,[C]_T)\) and a provably total functional graph \(\Gamma:C\to D\) to \([a_\Gamma]_T\). Identity and composition follow from graph equations; full faithfulness is provable graph equivalence, and coding plus the domain predicate supplies essential surjectivity. The restriction equivalence \(\operatorname{Par}(\mathcal B_T,\operatorname{Mono})\simeq\operatorname{Split}(S_T)\) sends a monic span \(C\xleftarrow m E\xrightarrow g D\) to \(gm^{-1}:C\rightharpoonup D\); its converse uses the split domain and the total restriction of a partial arrow. Pullback composition and restriction spans have the asserted graphs. The singleton terminal object of \(\mathcal B_T\) therefore supplies a restriction terminal object in \(\operatorname{Split}(S_T)\). **Evidence: derivation; status: verified.**

   The objects split here are **restriction idempotents**, not all idempotents. For \(e:X\rightharpoonup X\), the two arrows represented by \(e\) have types \((X,e)\to(X,1_X)\) and \((X,1_X)\rightharpoonup(X,e)\). Their composite on \((X,e)\) is its identity \(e\); only the first must be total. Coding identifies \((X,1_X)\) with \(U\). For every split arrow \(f:(X,e)\times U\rightharpoonup U\), its representative satisfies \(f=f(e\times1_\omega)\). The original Turing property gives total \(r:X\to\omega\), hence \(\overline{re}=e\), so \(re:(X,e)\to U\) is total and supplies the required parameter. The displayed factorization is composable throughout. Cockett–Hofstra §3.5, printed p. 195, supports this parameter argument; the manuscript separately establishes the terminal object that their general statement would assume in the starting category. **Evidence: derivation and citation; status: verified.**

3. **Section 7.4, p. 39; `08c-numerical-realization.tex:394–413`: substitution.** Proposition `prop:st-substitution-realization` is Proposition 5.7, whose statement and proof give PA-provable carrier and constructor equations for the same raw codes. It includes the retained original subtree and the quantifier branch that discards the computed body when the bound variable equals the substituted variable. The numerical arrows have precisely the displayed sources and targets in \(\mathcal C_{\mathrm{rec}}\); each is computed by a primitive-recursive traversal, restricted to its source carrier. This is totality **on that carrier**, not a claim that an arbitrary program is total on all numbers. PA-provable equations hold in \(\mathbb N\). The preceding argument independently proves initiality for every \(K_P\)-algebra in \((\mathcal C_{\mathrm{rec}}/P)^2\), and list initiality for every algebra in \(\mathcal C_{\mathrm{rec}}/P\), by terminating evaluation and uniqueness by induction. Thus uniqueness identifies the numerical folds without assuming that a realization functor preserves initial algebras. The pullback of the success injection \(\operatorname{Fm}\hookrightarrow1+\operatorname{Fm}\) then has the asserted admissibility carrier and induced map to \(\operatorname{Fm}\). **Evidence: derivation; status: verified.**

4. **Appendix A.1, p. 57; `a-syntax-and-theories.tex:155–160`: Cockett pinpoint.** Cockett's printed/PDF p. 7 defines the covariant functor \(I_Y:\mathcal X\to\mathcal X/Y\), \(X\mapsto(\pi_2:X\times Y\to Y)\), with the corresponding product action on morphisms. Lemma 2.2 identifies recursion in the slice, and Definition 2.3 requires preservation of recursion by \(I_Y\). This supports the manuscript's list-specific parameter statement. The footnote's p. 18 observation was checked independently: after the necessary typing corrections, the printed argument equates two composites through arbitrary target action \(g:A\times X\to X\), then invokes monicity of the source constructor \(r_1:A\times R\to R\) to cancel. That cancellation is unjustified. This does not prove Lemma 5.6 false, and neither p. 7 item depends on that later uniqueness argument. **Evidence: citation and derivation; status: verified.**

The total-map special case reduces the new definitions to terminal objects, ordinary products, and the stated retract criterion. The category with two objects and only one nonidentity arrow \(A\to B\) fails the retract condition for either proposed Turing object; it supplies no counterexample to the criterion. Partial functions give the expected restriction-terminal equation and distinguish totality in the original category from totality relative to a split domain. The separate \(\operatorname{Kar}\) convention agrees with Cockett–Lack, Proposition 2.26: its restriction is represented by \(\bar f e\); it is not substituted for restriction splitting in Section 5.1.

(E) Acceptance conditions, non-negotiable

No repair condition arises from a confirmed defect in these four changes. No claim in those passages must be dropped on the evidence checked here. This does not provide an acceptance recommendation for the whole manuscript.

(F) Not checked / uncertainty log

Read the entirety of Section 2; the Section 5.1 predicate equivalence, partial-inverse construction, and partial-map equivalence; the syntax/list/substitution dependencies of Proposition 5.7; the numerical parameterized syntax/list proofs; and adjacent Appendix A.1/substitution definitions. Visually inspected manuscript pp. 5, 15, 39, and 57 and Cockett–Hofstra pp. 189 and 195. The independent Cockett check visually inspected pp. 7 and 18 before comparing the existing p. 18 observation. Consulted *Mathematical Writing* §1 for the accompanying notation and exposition checks; no stylistic defect was promoted to a mathematical finding.

Did not audit the remainder of the manuscript, the incompleteness theorems, whole-paper novelty, Maietti's cited passage, or reconstruct a complete proof of Cockett's Lemma 5.6. Did not compile or modify the frozen source. This bounded audit cannot certify all external background results or every arithmetization detail.

Strongest confirmed blocker: none in scope. Strongest suspected but unconfirmed blocker: none exhibited in scope. Most important unchecked material: the remaining central theorems and their dependencies. The scoped conclusion does not depend on unavailable material. **Final recommendation: unknown for the whole manuscript; no rejection is supported by the four reviewed changes.**

---

# Mathematical-writing report

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

---

# Reconciliation of the reviews

# Reconciliation of the scoped Version 32 audit

**Conclusion.** No manuscript change is necessary on the evidence of these reviews. Neither report exhibits an actual defect in the four modified passages of *Logical consequence and essential incompleteness in recursion categories*, Version 32. No concrete unresolved finding in those passages warrants another audit pass. This is a bounded conclusion about the changes, not certification of the whole manuscript.

I read `hostile.md` and `writing.md`, checked the frozen LaTeX passages and their directly cited dependencies, and independently compared the relevant primary-source text: Cockett–Hofstra, §2.2, Theorem 3.4, and §3.5; Cockett, Lemma 2.2, Definition 2.3, and the printed Lemma 5.6 argument. I also consulted the supplied KLR *Mathematical Writing*, §1. The reviewers agree on the actual findings; their different report formats do not change the evidential conclusion.

## Findings and disposition

| Modified passage | Reconciled finding | Disposition |
| --- | --- | --- |
| §2.3, PDF p. 5; `02-categorical-preliminaries.tex:167–177` | Restriction terminal objects and cartesian restriction categories are defined before use. The total embedding and partial retraction, together with the Turing morphism, match Cockett–Hofstra's recognition criterion. The terminal equation is correctly typed. The omitted explicit equation \(!_1=1_1\) follows from uniqueness of total maps to \(1\). | No defect; retain. |
| §5.1, PDF p. 15; `05a-internal-syntax.tex:258–292` | The partial-map equivalence supplies the restriction terminal object. Restriction products and the object retractions are specified. For a split representative \(f=f(e\times1_\omega)\), the original total parameter \(r\) yields a parameter \(re\) that is total in the splitting, since \(\overline{re}=e\), and the displayed factorization follows. Cockett–Hofstra §3.5 supplies this argument; the manuscript independently establishes the cartesian hypothesis. It does not need \(S_T\) itself to be a Turing category in their stronger sense. | No defect or circularity; retain. |
| §7.4, PDF p. 39; `08c-numerical-realization.tex:394–413` | Proposition 5.7 proves the carrier and constructor equations in \(\mathrm{PA}\) for the same codes. These equations hold in \(\mathbb N\), and the preceding numerical proof independently establishes parameterized initiality. Uniqueness therefore identifies the numerical algorithms with the categorical folds. The admissibility pullback and sentence subobject have the stated types. | No missing inference; retain the transfer and uniqueness steps. |
| Appendix A.1, PDF p. 57; `a-syntax-and-theories.tex:148–160` | Cockett's Lemma 2.2 and Definition 2.3 concern recursion in slices and preservation by the product-to-slice functor, supporting the list-specific comparison. The p. 18 uniqueness argument improperly cancels through an arbitrary target action by appealing to monicity of the source constructor. This is a gap in that printed proof, not a demonstration that the lemma is false. The earlier cited items do not depend on it. | The pinpoint citation and user-requested footnote are supported; retain both. |

## Classification

- **Actual defects:** none established in scope.
- **Optional polish:** the writing reviewer suggests naming the ambient restriction category explicitly in the terminal-object definition and spelling out the directions of the two arrows represented by \(e\). Both are already determined by the surrounding definitions. They are optional additions, not repair requirements; no edit is recommended in this reconciliation.
- **Unsupported criticism:** neither reviewer presents a substantive criticism requiring dismissal. In particular, the reviewed text supports neither an objection that §5.1 presupposes a terminal object in \(S_T\) nor an objection that §7.4 assumes preservation of initial algebras by a realization functor. The requested footnote is a source-specific mathematical qualification, not editing-process narration.
- **Out-of-scope concerns:** the remaining central theorems, whole-paper novelty, Maietti's unchanged passage, and a complete replacement proof of Cockett's Lemma 5.6 were not audited here. They are not unresolved findings against these modifications.

The existing local outline and dependencies work; no reorganization is warranted. Preserve the explicit types, established terminology, substantive proof steps, and the appendix's categorical purpose. The hostile report's whole-manuscript recommendation and any format-imposed verdict labels neither certify correctness nor create a reason to reject the changes. No manuscript edits or external writes were made.
