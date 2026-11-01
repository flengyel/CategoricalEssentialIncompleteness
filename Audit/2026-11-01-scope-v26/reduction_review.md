# Reduction review of the version 26 scope audit

Baseline: *Logical consequence and essential incompleteness in recursion categories*, version 26, commit `490418a5eecbefa532e4d9283a7d504e4c611198`, 77 pages. This review combines the core, application-branch, hostile-referee and Mathematical Writing audit reports. It checks their recommendations against the result inventory and the relevant source interfaces. No manuscript text is changed.

**Current disposition, superseding every earlier scope option below:** retain all existing realization and application branches, including Miller, the syntactic application, the ordinary numerical first-order realization and the complete cosheaf construction. Retain all of Appendix A. Consolidate the shared numerical foundations once, using the strongest complementary arguments from §7.4 and Appendix B. No scope relocation has been chosen. Appendix D's comparison package remains only a possible future decision. The successive recommendations below are preserved as an audit history; the final constraint disposition governs.

## Consolidated recommendation

The reports agree that the largest savings require a scope decision. Most of the long proofs establish different universal properties, computational conditions or semantic comparisons. They are not removable repetitions.

The balanced main-paper option is a defensible recommendation: retain the comparison theorems, the categorical theory construction, syntactic and numerical realizations, standard and ultrapower soundness, indexed arithmetic theories and uniform independence, and the complete Miller application. Move the three-point construction with Appendix B to a companion treatment. Move Appendix D with the complementary-switch/source-comparison package of Lemma 6.2 and Corollary 6.3. Retain Appendix C with the lifting theorem and retain the first-order dependencies of Appendix A.

This retains a complete non-arithmetic first-order application while relocating the largest separate category-construction project. It removes about eighteen currently occupied pages, leaving roughly 59–60 before repagination and smaller consolidations. This is a block estimate, not a revised-PDF page count or a guaranteed minimum. A standalone companion must include or precisely cite its foundations and may therefore be longer than the pages removed from this manuscript.

The recommendation is not unanimous among the reviewers, and the final report should say so. The Mathematical Writing reviewer prefers this balanced choice. The branch and hostile reviewers support a more focused main paper moving both Miller and the three-point branch, as well as Appendix D, while treating those applications completely elsewhere. The core reviewer also identifies the numerical realization and ultrapower theorem as logically separable branches, but warns that moving them changes the paper's stated results. These are differences about mathematical scope, not conflicting correctness findings.

## The viable scope choices

| Option | Retained main-paper result beyond the arithmetic/syntax center | Current-page estimate and qualification |
| --- | --- | --- |
| Balanced main paper | Miller's representation-independent recursion category and real-closed-field application | Approximately 59–60 pages after moving the three-point branch, Appendix D and §6.1. It preserves a non-arithmetic first-order application. |
| Focused main paper | General theory construction and arithmetic realizations; optionally the compact one-model source-inseparability instance 6.3 | Approximately 54 pages if the compact §6.1 comparison stays; about one page less if it moves with D. Both non-arithmetic application branches move, so claims about what the main paper itself demonstrates must narrow. |
| Representation-focused main paper | The full three-point example, including categorical non-equivalence and failure of decidable equality on its universal object | Roughly 67–68 pages after moving Miller and the full model-family comparison. The expensive compatible Turing-morphism and completion proofs remain necessary. |

Miller and the three-point example do not prove the same distinction. Miller supplies a complete logical application under a representation-independent computability condition and a separation phenomenon after fixing a representation. The current text does not prove for it the three-point branch's categorical non-equivalence with ordinary recursion. If that categorical representation distinction is the principal target, retain the three-point example or make its complete companion treatment part of the declared publication scope.

## Findings on which the reports agree

1. **Two arithmetic routes must remain distinguished.** The direct syntactic route is 3.1 to 4.2 to 7.3, using the internal realization, standard soundness, reduction and partial proof-search lift. The source-inseparability route uses 3.5 and then 4.3. The uniform theorem 7.6 needs the indexed family and one parameterized computation. It is not obtained merely by selecting one sentence separately for every theory.

2. **Numerical realization is a separate proof obligation.** Proposition 7.7 proves initiality for arbitrary extensional computable algebras. The §5 realization uses provability-controlled graphs and equations in a different category. The standard interpretation's preservation of finite limits and images does not supply preservation of initial algebras. A unifying computational-fold theorem would be additional mathematics, not an existing economy cut.

3. **The ultrapower result is additional mathematics.** Standard soundness does not by itself cover the entire interpreted nonstandard proof carrier. Moving §6.4 requires moving the ultrapower clause of Theorem 7.3 as well. The balanced recommendation retains that accepted contribution rather than removing it on a citation-count argument.

4. **Reference counts do not determine relevance.** Proposition 7.7 is semantically used in its own ensuing construction and numerical application despite having no literal theorem-label consumer. Terminal theorems such as 7.6, 8.6, 9.6 and B.10 are purposes of branches. Appendix C is cited by its section label. The inventory correctly needs manual mathematical roles in addition to literal citations.

5. **The proposed moves have dependency packages.** The cosheaf observation theorem uses `Pair(Rec)`, currently defined in §7.6. Its category construction also needs the numerical base and numerical partial-map comparison. Its propositional theory requires subsection §A.6, the general inference functor, the least-image theorem and the range/image bridge. Moving §9 without its Appendix B and these interfaces would strand definitions and proofs.

6. **Appendix C supports a substantive main claim.** It shows why section lifting cannot be omitted, rather than merely providing an optional example of the positive theorem. Keep it if that necessity claim remains. Its disjoint-arrow nonexistence result also distinguishes arrow joins from idempotent joins.

## Confirmed consolidation opportunities

The following remove repeated mathematics within the current combined manuscript. Their savings are local; none justifies a large page promise.

- **One numerical base category.** Align the category used in §9 with the explicitly typed `C_rec` of §7.4. Then replace Appendix B's second proof of numerical finite limits, images, preimage descent and regularity by a reference to Proposition 7.7. Retain the componentwise naturality, descent and finite-probe arguments for the fork category: those are new.
- **One numerical partial-map equivalence.** Appendix B reconstructs a numerical equivalence in the reverse direction from the one in §7.4. Consolidate its typed quasi-inverse data and proof in one place. The reverse direction is an equivalence, not a literal inverse function; name the chosen object and arrow assignments before reusing it.
- **One proof of fork local connectedness and non-equivalence.** Keep the complete proofs in Appendix B and replace the repeated main-text arguments in §9.1 by precise result references and the conclusions needed for the application.
- **Remove or relocate minor repeated introductions.** The generic arithmetic example at the end of §5.4 is repeated by the actual setup in §7.1. The Bernardi comparison is contextual related work, not a premise of the final numerical construction; preserve its restricted claim and citation if moving it to that discussion.

The writing report's proposal to reuse numerical diagonal-pair arguments across §7.5 and the cosheaf endpoints needs a qualification: the specified endpoint Turing morphisms and their diagonal pairs are not automatically the same chosen numerical data. Consolidate common target-category verification or apply the existing general theorem concisely; do not identify the pairs without a proved comparison or reduction. This is a conditional economy proposal, not an immediate deletion.

## Corrections in the synthesis

- **Theorem A.6 and subsection §A.6 must be distinguished.** The former is the first-order theorem result. The latter is the propositional specialization used by the three-point branch. The revised CSV now uses §A.6 when it means the subsection.
- **Current dependencies and proposed consolidations must be distinguished.** Appendix B currently reproves its numerical base and the unnumbered `Q_num` equivalence. It does not currently cite Proposition 7.7 for them. The revised CSV records that current proof interface and separately notes the consolidation opportunity.
- **Corollary 6.3 is a one-model result.** An earlier core-report table described it as interpretation in all models. The source states the result for each chosen model M; Appendix D constructs the all-model family. The final core report and synthesis now make this distinction correctly.
- **Keeping 6.3 is a choice of endpoint, not a logical necessity.** If the focused option still retains numerical §7.5, Theorem 3.5 has that numerical application even if §6.1 moves. Keeping 6.3 has the separate value of applying the lifting theorem to the generally non-locally-connected syntactic source. In the balanced option, Miller supplies another substantial use of 3.5.
- **No scope choice is consensus-by-count.** The final outline should state why the balanced option is recommended and record the stronger representation reason for retaining the three-point branch as the principal alternative.
- **Machine headings need complete titles and pages.** The original regex truncated §8.2's nested TeX title and left unlabelled heading pages empty. The parent reports that the heading extraction now uses balanced braces and auxiliary-table page information. These are indexing repairs, not manuscript changes.

The CSV is suitable as an interface and placement inventory. Its literal-reference columns are not a formal proof-dependency graph; its semantic prerequisites are reviewed mathematical interfaces, not a claim of minimality or Lean dependency closure. That distinction must accompany any exported table.

## Acceptance endpoint for the proposed shorter outline

The balanced outline passes this scope audit if the final report preserves these conditions:

1. State the retained contribution and the loss of the full three-point representation result from this main article; keep that result complete in its companion package.
2. List the unnumbered definitions and comparison data that travel with each move, especially `Pair(Rec)`, the numerical partial-map comparison and propositional inference construction.
3. Preserve every retained realization's typed arbitrary-algebra fold, computability/domain invariant, equations and uniqueness argument; do not infer initiality preservation without proof.
4. Keep Appendix A's first-order dependencies self-contained and its numerical realization proofs in the application sections. If the propositional-only subsection moves, its dependent generic image machinery remains available in the companion.
5. Keep Appendix C while advertising necessity of lifting. Retain the standard/ultrapower distinction and any other qualification attached to a retained theorem.
6. Reconcile the final abstract, introduction, §4's concluding application paragraph and roadmap with the chosen scope during implementation, respecting the author's instruction to revise the front matter last.
7. Treat page totals as estimates until the proposed assembly is actually built. No actual reduction, new compilation or Lean formalization is established by this audit alone.

No false theorem or new mathematical obstruction is identified by this synthesis. The remaining decision is the paper's scope and organization, not a missing proof introduced to justify shortening.

## Final synthesis check

I read the final `scope_and_length_audit_v26.md` and the revised 66-row CSV. The balanced recommendation, focused alternative, representation-focused alternative, companion dependency packages and approximate page quantities are consistent with the source-based findings. The report does not count duplicated cosheaf proofs as an additional saving after moving the whole cosheaf branch. It distinguishes the arithmetic routes, preserves the ultrapower clause's dependencies, and does not infer preservation of initiality from regular interpretation. The CSV distinguishes current numerical facts reproved in Appendix B from the proposed consolidation at Proposition 7.7. The core report's one-model wording has been corrected.

**Final disposition: the scope and dependency audit passes this reduction check.** No necessary correction remains in the final report or table within this review's scope. This disposition does not implement a shortening, certify every mathematical proof, establish novelty, or verify Lean code.

## Superseding addendum: retain the cosheaf construction

The author's subsequent scope instruction requires the complete three-point cosheaf application in the main paper. That instruction supersedes the preferred balanced and focused options above wherever they move §9 or Appendix B. Those earlier dispositions concern an earlier scope proposal and are not approval of the revised scope. Retain §9, its full structural dependencies in Appendix B, and Appendix A including its propositional specialization in §A.6. The categorical non-equivalence result and the absence of decidable equality on the universal object belong to this retained construction.

This leaves two substantive shortening decisions. Moving Miller §8 as a complete package removes about six currently occupied pages. Moving the independent faithful-family branch in Appendix D together with Lemma 6.2 and Corollary 6.3 removes about three to four. Proposition 6.1, the regular total interpretation, and the standard/ultrapower soundness proofs stay: the numbered subsection §6.1 is not the whole interpretation construction. With cosheaves retained and these packages moved, the earlier representation-focused estimate remains roughly 67–68 current pages. Keeping Miller instead is a coherent broader scope, with correspondingly less reduction.

### An additional, dependency-checked split of the numerical branch

The full ordinary numerical first-order realization is not needed to establish the retained cosheaf realization. It is distinct mathematics, not a duplicate. It can nevertheless move with the numerical arithmetic benchmark if the main paper no longer claims that ordinary numerical first-order realization as one of its proved representations. The following boundary preserves the cosheaf construction.

| Retain in the main paper | Move together if this scope option is chosen |
| --- | --- |
| `08c-numerical-realization.tex`, lines4–35: `Rec`, its extensional partial-function interpretation, the dimension/carrier presentation of `C_rec`, and the tuple codings | The first-order assertions at lines52–60 of Proposition 7.7 and their proof at lines211–393: parameter-stable syntax and list initiality, free variables, admissible substitution, and initial derivations for arbitrary axiom subobjects |
| The structural assertions of Proposition 7.7 and their proof at lines62–209: total splitting equivalence, regularity and disjoint stable coproducts, monomorphisms, and the restriction equivalence between monic spans and the splitting | Lines396–515: the numerical arithmetic objects, the typed rule-label and proof-tree code comparisons with the standard interpretation of the syntactic category, and the resulting numerical theorem object |
| The definition `J_rec: Rec -> Pfn` at `08d-numerical-incompleteness.tex`, lines28–31; its carrier convention is used explicitly in Appendix B | The remaining numerical arithmetic application of §7.5, with its chosen diagonal pair, the arithmetic domain inclusions and numerical incompleteness conclusion |
| The definition of `Pair(Rec)` at `08-essential-incompleteness-of-arithmetic.tex`, lines300–306, separated from the arithmetic example around it | The arithmetic numeral-observation functor and its inseparability conclusion in the rest of §7.6; the final Bernardi comparison can travel with that argument or be integrated into related work |
| The explicit numerical comparison `Q_num: Split(Rec) -> Par(C_rec,Mono)` used in §9 and Appendix B, or a specified quasi-inverse to the retained equivalence with its arrow assignments and comparison isomorphisms | No cosheaf component fold, naturality proof, component consistency argument or endpoint inseparability proof |

The split requires dividing Proposition 7.7 into a retained structural proposition and a first-order realization proposition in the moved package. Deleting its proof tail while retaining its full current statement would leave an unproved assertion. Similarly, §7.5 cannot move as a whole file without first retaining the definition of `J_rec`, and §7.6 cannot move as a whole without first retaining `Pair(Rec)`.

The retained foundations should be placed before their first use in the cosheaf application or gathered into a clearly cited numerical-foundations subsection. Their present placement inside an arithmetic subsection is not a necessary dependency. No new general theory of computational folds is needed for this split.

### Dependency verification for this option

I checked all literal references and the relevant construction interfaces of §9 and Appendix B. Neither uses the first-order tail of Proposition 7.7, the arithmetic proof-code bijection, the numerical arithmetic theorem object, or the numerical arithmetic incompleteness conclusion. Their apparent references to the arithmetic section resolve to three smaller interfaces: the definition of `J_rec`, the definition of `Pair(Rec)`, and an example of the complementary-domain switching construction. The latter switch is already proved directly for the endpoint category in §9, lines313–324; its backward allusion can be removed or redirected without omitting a mathematical premise.

The endpoint comparison uses `C_rec` and its monic-span category, the explicit `Q_num` equivalence, and the specified cosheaf Turing morphism. Its diagonal pair is established in that endpoint category. The propositional syntax and proof folds are proved directly in the functor category, including naturality, before applying Appendix A's least-image theorem and the range/image bridge. These arguments do not use the moved ordinary numerical first-order fold. Conversely, the syntactic first-order realization and the direct arithmetic route in §§5–7.3 remain unchanged by moving the numerical benchmark. This check does not infer preservation of an initial algebra by an interpretation functor.

### Revised estimates and acceptance conditions

The movable numerical first-order/arithmetic material occupies approximately four additional current pages: it begins partway through page38, while shared structural numerical material remains through that page, and ends on page42. This is a page-block estimate, not an exact saving. Together with moving Miller and Appendix D's package, it suggests a main paper in the vicinity of 63–64 current pages before repagination and small consolidations. Retaining the numerical benchmark instead gives the roughly 67–68 page option. Keeping Miller adds its approximately six-page branch to the relevant option.

The repeated numerical base proof and numerical partial-map equivalence in Appendix B can still be consolidated with the retained structural proposition. The componentwise descent, cosheaf naturality, finite connected probes, compatible Turing morphism and completion proofs cannot. The repeated local-connectedness and non-equivalence proofs in §9 can become statements with precise references to their complete Appendix B proofs. These are modest further savings and should not be promised as a fixed number of pages.

The revised scope passes this dependency review provided that (1) all cosheaf and Appendix A dependencies remain; (2) `Rec`, `J_rec`, `Pair(Rec)` and the required numerical equivalence survive any numerical-branch move; (3) Proposition 7.7 is split rather than partially proved; (4) claims of an ordinary numerical first-order realization move with their proof if that option is adopted; and (5) the final page estimate awaits compilation. This addendum approves a dependency boundary, not a completed shortening or a full correctness certificate for the manuscript.

## Final disposition on the revised root report

I reread the revised `output/scope_audit_v26/scope_and_length_audit_v26.md` and its regenerated 66-row dependency CSV. The recommendation now conforms to the author's required scope: consolidate first, keeping the full cosheaf construction, Miller application, ordinary numerical first-order realization and all of Appendix A. The faithful-family comparison and Lemma 6.2/Corollary 6.3 are identified as the first possible relocation, not as prerequisites of retained soundness. The CSV's recommended column consistently keeps 62 numbered items and moves only those four items; its optional smaller-scope column retains every cosheaf and Appendix A item.

The numerical split preserves the structural proposition, `Rec`, `J_rec`, `Pair(Rec)`, numerical Turing universality and the specified partial-map comparison. It explicitly moves the ordinary numerical first-order claims with their proofs and requires splitting Proposition 7.7. The cosheaf endpoint and naturality arguments stay complete. Miller's distinct conclusions are not attributed to the cosheaf construction. The estimates 73–74, 69–70 and 63–64 refer consistently to successive block relocations before the smaller consolidations; none is presented as a compiled page count.

**Final disposition: the revised report and table pass this synthesis and dependency-boundary review.** I found no further necessary correction or hidden missing dependence within the proposed moves. The earlier preferred options that removed cosheaves are superseded. No root report, manuscript source or Lean file was edited by this review, and the disposition does not certify every theorem or an implemented shortening.

## Final constraint disposition: all applications remain

The author's latest instruction retains Miller, the historically necessary syntactic application, the numerical realization and the full cosheaf construction. Consequently no earlier option to relocate Miller, the numerical logical case or cosheaves is a current recommendation. The primary task is now consolidation without loss of mathematical scope. Appendix D, Lemma 6.2 and Corollary 6.3 remain in the manuscript unless a later scope decision relocates them; the audit does not select that move. All 66 numbered items should therefore be marked as retained in the primary-action column. No estimate obtained by subtracting a moved branch describes the currently chosen revision.

### One numerical foundation: retain the best arguments from both proofs

The following specifies the proof content to keep once. Source line numbers refer to the unchanged version 26 files.

| Mathematical interface | Retained construction or proof |
| --- | --- |
| Category and carrier types | Keep `08c-numerical-realization.tex`, lines4–35: the extensional category `Rec`; `C_rec` objects `(m,C_0)`; arrows total on their specified c.e. carriers; the separate carrier notation; fixed injective tuple codings `kappa_m`, their recursive images and inverse domains. Use this presentation in §9 instead of its second, less explicitly typed definition. Define `J_rec` once with this numerical foundation, or give its existing definition a precise forward reference until it is relocated. |
| Finite limits | Keep §7.4's dimension-aware terminal object, tuple products and c.e. equalizer construction, including the universal arrows and the halting-on-source argument. Appendix B should cite this base result rather than repeat it. |
| Coproducts and extensivity | Keep §7.4's concrete even/odd tagged carrier, injections and computable copairing, with the tag-based inverse-image decomposition. Retain the slice-equivalence conclusion explicitly, as Appendix B's argument currently does for the fork category; that category still needs its natural componentwise decomposition. A bare reference to tags should not replace the universal property. |
| Regular images and descent in the numerical base | Keep §7.4's dimension-aware image object and complete characterization of regular epimorphisms as carrier-surjections. Incorporate Appendix B's explicit section algorithm for a base surjection `q:C -> D`: enumerate the source and search for `q(x)=y`, defining a computable `s:D -> C` with `q s=1_D`. Descending a map constant on the fibers then uses `h s`, with independence and uniqueness stated once. Keep pullback stability on the c.e. pullback carrier. This combines B's useful section statement with §7.4's complete regularity conclusion, rather than keeping two proofs. |
| Monomorphisms and partial inverses | Keep §7.4's singleton-test proof that monomorphisms are precisely carrier-injective arrows, followed by preimage search and the typed equations for `mu_m`. These give the exact partial inverse needed by the monic-span construction. Appendix B may cite the base inverse and must separately retain its componentwise probe argument for monomorphisms in `C_rec^J`. |
| Total splitting comparison | Keep §7.4's explicitly typed functors `Q:C_rec -> Tot(Split(Rec))` and `F` in the reverse direction, their exact-domain checks, and the displayed natural isomorphisms `u:FQ => 1` and `v:QF => 1`. This is stronger and more reviewable than an unexplained existence assertion. |
| Partial-map comparison | Keep §7.4's span formula `widetilde Q[m,g]=Q(g) mu_m`, invariance under isomorphism of spans, compatibility of pullback composition with partial-function composition, restrictions, fullness, faithfulness and essential surjectivity. This is the complete proof interface missing from a bare carrier-function description. Keep Appendix B's useful explicit reverse functor `Q_num` as specified quasi-inverse data, with object `(1,D_e)` rather than an untyped subset `D_e`, and its arrow represented by the c.e. domain span and restricted decoded function. |
| Comparison in the reverse direction | Use tuple decoding and the carrier bijections to give the corresponding comparison isomorphisms for `Q_num widetilde Q` and `widetilde Q Q_num`. Check their naturality on partial arrows, not only total ones. Once this is done, omit Appendix B's second independent full-faithfulness and essential-surjectivity proof. The functors point in opposite directions and are not literal inverse functions. |

The regularity section algorithm is a fact about the numerical base. It does **not** choose a natural section of a componentwise surjection in the fork category. Appendix B must retain the separate naturality proof for the descended component maps: from the component descent equations, the existing displayed chain gives equality after composing with the surjective `q_0`, and cancellation proves naturality. It must likewise retain the `H_j` probe argument, the component image-subfunctor check and the natural coproduct decomposition. These are the additional mathematical content of its regular/extensive functor-category result.

One organizational implementation is to state a numerical structural proposition before the ordinary numerical first-order realization, with both remaining in the paper. Appendix B then starts its structural proof by invoking that proposition and proves only the fork-specific consequences. Section 9 cites the same foundation and the fork results. If the current Proposition 7.7 is divided for this purpose, both its structural and logical assertions remain proved; this is organization, not scope reduction. Numerical and syntactic folds continue to have separate proofs in their application categories.

The independent first-order derivation, substitution and proof-code comparison arguments remain complete. Miller's representation-independent computation, its fixed-representation separation and its first-order application remain complete. The cosheaf compatible Turing morphism, completions, non-equivalence, absence of decidable equality, natural propositional folds and consequence objects remain complete. Appendix A retains its self-contained categorical construction and does not absorb these realization proofs.

**Governing disposition:** the next revision should implement only the confirmed consolidations while preserving every current branch and theorem claim. No Miller move, numerical-realization move or cosheaf move is recommended. The earlier reduction estimates are historical alternatives, not targets or promises for this revision. This review has made no manuscript edits.

## Definitive validation of the final audit artifacts

I read the latest root report, `output/scope_audit_v26/scope_and_length_audit_v26.md`, and the regenerated dependency table, `output/scope_audit_v26/result_dependencies_v26.csv`, after their consolidation-only revision. They match the governing disposition above. Every one of the 66 numbered items has a primary action beginning with `Keep` (44 general items, 6 Miller items and 16 cosheaf items). Neither the ordinary numerical first-order realization nor any application is selected for relocation. The faithful-family package is identified only as an unchosen future scope possibility.

The root report's numerical-foundation table concretely retains the explicit category/carrier conventions, universal constructions, surjection sections and descent, monomorphism inverse search, total equivalence data, complete monic-span comparison and specified reverse equivalence. It preserves the separate fork naturality and probe obligations and all first-order and propositional realization proofs. The report assigns no shortened page count and clearly distinguishes the audit from a manuscript revision. I found no missing mathematical dependence or inconsistent selected action in these changed artifacts.

Two minor residual CSV placement phrases were reported to the parent for clarity: replace B.2's conditional “if kept in same paper” by the affirmative shared-foundation consolidation, and replace 9.5's reference to “every numerical-branch scope option” by retention of the common `Pair(Rec)` and `J_rec` interfaces. Neither changes the dependency finding or the all-retained actions.

**Definitive disposition: the final consolidation-only audit passes this synthesis check.** This is validation of the changed audit artifacts and their proposed proof interfaces, not a new review of the unchanged manuscript. No root artifact or manuscript source was edited by this agent.
