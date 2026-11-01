# Scope and length audit of version 26

**Recommendation:** retain the Miller, syntactic, numerical and cosheaf realizations and their applications. Consolidate the numerical foundations into one proof, combining the explicit category and equivalence data of §7.4 with the useful section and descent arguments of Appendix B. Consolidate the other genuinely repeated arguments listed below. No application is selected for removal.

The cosheaf example has a particular role in the paper: Proposition B.10 distinguishes its restriction category from ordinary recursion and proves that its universal object has no decidable equality. Its propositional consequence objects therefore address representation beyond the numerical prototype. Heller explicitly sought “examples substantially different in spirit from the prototype” [Heller 1990, introduction]. This is a reason to retain the construction, rather than judge it solely by its length.

This report audits *Logical consequence and essential incompleteness in recursion categories*, version 26, 77 pages, at commit `490418a5eecbefa532e4d9283a7d504e4c611198`. All 23 modular source files match that commit. Four independent reviews cover the core dependencies, application branches, mathematical writing, and the risks of shortening; a fifth reconciles their conclusions. Their subsequent addenda retain the cosheaf, Miller and syntactic applications. The final recommendation supersedes earlier proposals to relocate those applications. The mathematical manuscript has not been edited.

## Current outline

Page ranges overlap where a section starts partway through a page. They measure current occupied blocks, not the eventual length of a revised document.

| Current part | Contents and mathematical function |
| --- | --- |
| Abstract and §1, pp.1–3 | Scope and literature. The present introduction still calls Miller the principal application and describes the older all-model route; its roadmap is out of date. Rewriting remains deferred until the scope is settled. |
| §2, pp.3–4 | **2.1** partial maps, restriction idempotents, ranges, splittings and inseparability; **2.2** products, coproducts and local connectedness; **2.3** recursion categories and Turing morphisms. Shared hypotheses and conventions. |
| §3, pp.4–7 | **3.1** diagonal comparison and lifted separators; **3.2** target conditionals from local connectedness and source inseparability when they lift; **3.3** a sufficient join condition for lifting. Two related comparison mechanisms. |
| §4, pp.7–10 | **4.1** consequence objects, ranges, and interpretation; **4.2** incompleteness from semantic consistency; **4.3** incompleteness from an inseparable source pair. These are the two routes used by later applications. |
| §5, pp.10–23 | Define the syntactic recursion category and computation coding. **5.1** predicate presentation and categorical structure of its total splitting; **5.2** parameterized syntax and lists; **5.3** free variables and substitution; **5.4** initial derivations and generated theories. This realizes Appendix A using provable graph equality and totality. |
| §6, pp.23–28 | Define the model functor. **6.1** a source-complementarity switch and a source-inseparability instance; **6.2** regular total interpretation; **6.3** substitution and soundness on standard proof codes; **6.4** the ultrapower comparison and full interpreted-proof soundness. |
| §7, pp.28–42 | **7.1** fixed syntactic arithmetic comparison; **7.2** indexed theory family and numeral fibers; **7.3** uniform independent sentences; **7.4** ordinary numerical realization and proof-code comparison; **7.5** numerical incompleteness; **7.6** numeral observations, extensions and the pair category. |
| §8, pp.42–48 | **8.1** computation uniform across representations and its recursion category; **8.2** inseparability of the two Miller cuts and separation after fixing a representation; **8.3** first-order realization and a real-closed-field theory. A complete application branch. |
| §9, pp.48–55 | Construct the three-point category. **9.1** local connectedness and lifting; **9.2** evaluation functors and endpoint computation; **9.3** propositional syntax, initial derivations, consistency, observations and essential incompleteness. Full structural proofs are in Appendix B. |
| Appendix A, pp.55–64 | **A.1** categorical hypotheses, Boolean morphisms, conditionals and parameter stability; **A.2** syntax, free variables and sentences; **A.3** admissible substitution; **A.4** inference algebras and least closed images; **A.5** first-order theories and the image/range interface; **A.6** the propositional specialization. Its job is the categorical construction of theories. |
| Appendix B, pp.64–71 | **B.1** cosheaves, fork diagrams and the regular total category; **B.2** partial maps, ranges and local connectedness; **B.3** the universal object and frames; **B.4** a coherent Turing morphism; **B.5** the generated recursion category, splittings and non-equivalence with ordinary recursion. Required structural development for §9. |
| Appendix C, pp.71–74 | A recursion-category counterexample when section lifting is omitted, including the absence of a common upper bound for two disjoint-domain arrows. Supports the sharpness discussion in §3. |
| Appendix D, pp.74–76 | Faithful interpretation in all countable models; **D.1** source pairs under ambient theory extension; **D.2** numeral observations; **D.3** a complete ambient theory. An independent comparison branch. References follow. |

The accompanying CSV inventories all **66 numbered results and definitions**. It separates literal citation locations from the mathematical interfaces used in this scope audit. A terminal result can justify its own section without being cited later. Conversely, a result can be used through surrounding constructions without a literal reference to its label: Proposition 7.7 is a clear example.

## Dependencies that determine the scope

The main arithmetic argument uses the direct comparison mechanism:

- Appendix A supplies categorical syntax, inference algebras and the least closed image theorem.
- Theorem 5.9 realizes those objects in the total restriction splitting of the syntactic category.
- Proposition 6.6 supplies standard-code soundness. Lemmas 6.7–6.8 and Theorem 6.9 extend its factorization to the full ultrapower interpretation.
- Lemmas 7.1–7.2 provide the reduction and partial proof-search lift. Theorem 4.2 then gives Theorem 7.3. Corollary 7.4 gives recursive inseparability of the ordinary theorem/refutation sets.
- Proposition 7.5 and the preceding family construction identify the indexed fibers. Theorem 7.6 gives uniform independent sentences, using the standard soundness and computational diagonal data.

Theorem 7.3 does not use Theorem 3.5's source-inseparability route. Theorem 7.6 also does not require the ultrapower extension. Nevertheless, the ultrapower results are required for the explicit ultrapower clause of Theorem 7.3. Removing them would narrow that theorem, rather than remove a repeated proof.

The source-inseparability route is separate: Theorem 3.5 supplies an inseparable pair, and Corollary 4.3 places it below theorem and refutation domains. Numerical §7.5, Miller §8 and cosheaf §9 use this route. Corollary 6.3 remains a useful further instance for a syntactic source that need not be locally connected, but it is not a missing premise of the arithmetic soundness argument.

### Proofs that must not be treated as duplicates

1. **Syntactic and numerical initiality.** In the syntactic category, graph equality and the relevant totality statements are proved in the ambient theory. In the numerical category, the target algebra may have operations total on their c.e. carriers without PA proving that totality. Both folds need their own existence and uniqueness arguments. The standard interpretation does not automatically preserve initial algebras.
2. **The abstract construction and its realizations.** Appendix A assumes the specified initial algebras. Each application must establish them in its own category. Appendix A's least-image theorem does not supply a missing derivation algebra.
3. **Standard and ultrapower soundness.** Induction on standard finite derivations does not by itself cover every nonstandard interpreted proof code. The natural comparison and transported factorization are additional mathematics.
4. **Componentwise and functor-category initiality.** The cosheaf realization must prove that the component folds are natural. Initiality in separate components alone is insufficient.
5. **Different lifts.** Lemma 6.2 constructs a source-total switch from predicates proved complementary in the source. Lemma 7.2 constructs a partial source search whose interpreted behavior is exact under target disjointness. The two hypotheses and roles must remain distinct.

## Confirmed consolidation opportunities

These are safe targets for a subsequent revision, with the comparison data preserved. They have not been applied.

| Source anchor in v26 | Repetition | Proposed action and retained obligation |
| --- | --- | --- |
| Appendix B, lines87–110, versus §7.4 numerical foundations | Terminal object, equalizers, images, surjective descent and pullback stability in the same numerical base category | Combine the best numerical arguments in one structural proposition before the first-order part of §7.4. Cite it in Proposition B.2; retain the latter's componentwise construction and naturality of descent, which are new. |
| Appendix B, lines608–647, versus §7.4 partial-map equivalence | A second numerical comparison between the restriction splitting and the monic-span category | Consolidate at one numerical foundation. The functors currently point in opposite directions; retain a specified quasi-inverse, its action on partial maps, and the comparison isomorphisms. Do not silently write a literal inverse of an equivalence. |
| §9, lines41–45 | A second definition of the numerical base category with less explicit carrier conventions | Refer to the dimension/carrier presentation already fixed in §7.4 and use its object/carrier distinction consistently. |
| §9, lines146–155, versus Proposition B.4 | Repeated connected-probe argument | State the verified structural properties and cite B.3–B.4 in the application. Keep the proof in Appendix B and the subsequent application of lifting in §9. |
| §9, lines163–171, versus Proposition B.10 | Repeated five-versus-two subobject argument | State non-equivalence once in the application and retain its full proof once in Appendix B. |
| §5.4, final paragraph, lines872–878 | A preliminary arithmetic instance immediately followed later by the actual arithmetic construction | Delete the preliminary instance or replace it by one forward reference. Theorem 5.9 and the full setup in §7.1 remain. |
| §7.6, final Bernardi paragraph | A technical comparison after the application sequence | Relocate to related work if it adds a specific distinction beyond the existing paragraph there. It is not a proof prerequisite. Preserve the exact limited comparison and its citation. |

These consolidations preserve the cosheaf construction. Their saving is modest: the componentwise descent, finite probes, coherent Turing morphism, completion arguments and naturality of the syntax and proof folds are distinct obligations. No fixed page saving is assigned before compilation.

Several further proposals need a mathematical decision before becoming cuts. The word-frame construction is part of the chosen generated cosheaf recursion category; deleting it changes that construction. The Karoubi-envelope comparison is stronger than the restriction-splitting claim needed by the logical objects; deleting it narrows the stated completion result. A new general theorem unifying the several computable-fold proofs could be useful, but it would require its own typed framework and proof and is not an established page saving.

## One numerical foundation

The first consolidation should produce one numerical-foundations subsection before the numerical first-order realization. It should contain the following material once.

| Material to use | Best current location | Function in the consolidated proof |
| --- | --- | --- |
| Objects `(m,C_0)`, carrier notation, computable maps, fixed tuple codings | §7.4, `08c-numerical-realization.tex`, lines4–35 | One precise category convention for every later numerical and cosheaf use |
| `Q: C_rec -> B_rec`, `F: B_rec -> C_rec`, and natural isomorphisms `u: FQ => 1` and `v: QF => 1`, where `B_rec = Tot(Split(Rec))` | §7.4, lines63–111 | Explicit total equivalence with its object and arrow assignments and decoding comparisons |
| Dimension-correct terminal object, products and equalizers; tagged coproduct injections and actual copairing | §7.4, lines113–141 | Concrete universal properties, disjointness and pullback stability |
| Typed image object, surjective image factorization, coequalizer descent and stable surjections | §7.4, lines143–163, supplemented by Appendix B, lines97–110 | One regularity proof; include Appendix B's explicit computable section for a numerical surjection as the mechanism for descent |
| Numerical monomorphisms as injections, inverse search on the image and the typed partial-inverse equations | §7.4, lines165–176 | The bridge to restriction monomorphisms and partial maps |
| `Q_tilde: Par(C_rec,Mono) -> Split(Rec)`, its span action, composition, fullness, faithfulness and essential surjectivity | §7.4, lines178–210 | One complete restriction-equivalence proof |
| The reverse functor `Q_num: Split(Rec) -> Par(C_rec,Mono)` required by the final non-equivalence argument | Appendix B, lines608–647 | Specify it as a chosen quasi-inverse, including the object `(1,D_e)`, its partial-arrow action and comparison isomorphisms; use the established equivalence rather than repeat its full proof |

The section should also supply `J_rec: Rec -> Pfn` and its preservation properties, now introduced only in §7.5. The definition of `Pair(Rec)`, currently in §7.6, remains available for the cosheaf observation theorem. Relocating these definitions next to their common foundations or first common use would improve reading order without removing their arithmetic examples.

The best arguments in Appendix B are not all numerical duplicates. Retain its proof that component images form a subfunctor, its naturality equation for descent through a componentwise surjection, its finite probes detecting component monomorphisms, and its tagged-subfunctor proof of extensivity. Computable sections in the numerical base need not form a natural section of a fork morphism. Descent in the fork category must still be justified by its existing equation and cancellation through the surjective component. This distinction prevents the consolidation from suppressing a proof obligation.

Splitting Proposition 7.7 into a numerical structural proposition and a first-order realization proposition would give each statement one mathematical purpose. Both propositions and their complete proofs remain in the paper. The syntax, lists, substitution and derivation folds, and the arithmetic proof-code comparison remain separate from the structural proof; none follows merely from regularity or equivalence of the underlying total categories.

## Retained applications and organization

The applications answer different questions and remain complete.

| Application | Role in the paper | Material to retain |
| --- | --- | --- |
| Syntactic category `S_T` | Applies the internal construction to the historical syntactic setting and supplies the soundness, arithmetic and uniform-family results | §§5–7.3, with typed predicate, syntax, substitution, derivation, interpretation and fiber comparisons |
| Ordinary numerical recursion | Establishes the extensional first-order realization and its precise comparison with interpreted syntactic codes | Numerical logical part of §7.4 and applications §§7.5–7.6, following the single shared structural foundation |
| Miller sequences | Provides a non-arithmetic first-order application and proves how separation changes after a representation is fixed | All of §8: representation space, compactness computation, recursion category, diagonal reduction, first-order realization and real-field model |
| Three-point cosheaves | Represents propositional consequence in a category distinguished from ordinary recursion, with no decidable equality on its universal object | All of §9 and Appendix B; retain the coherent Turing morphism, completion comparisons, natural folds, consistency and endpoint observations |

Appendix A retains its single job: categorical construction of the theory objects. Keep its propositional specialization in subsection §A.6, as well as the inference-algebra, least-image and range/image results it uses. Subsection §A.6 is distinct from the numbered first-order Theorem A.6. Numerical realization proofs remain where the appendix is applied.

The broad section order can remain as it is. Within it, separate the numerical structural proposition from the first-order realization statement, and replace repeated structural proofs by precise references. The full cosheaf local-connectedness and categorical-distinction proofs stay once in Appendix B; §9 states the needed conclusions and applies them.

The faithful-family comparison in Appendix D, with Lemma 6.2 and Corollary 6.3 in subsection §6.1, is independent of the main one-model soundness and arithmetic route. This identifies an optional future scope choice, not a selected cut. Proposition 6.1, total interpretation, standard soundness and ultrapower soundness have distinct retained roles. Appendix C remains with the claim that lifting cannot be omitted. No material is marked for removal in the recommended-action column of the dependency table.

The historical distinction concerns the comparison itself. The attempted comparison between $S_T$ and the pointwise system $S′_T$ cannot be a comparison of categories, because the proposed composition in the latter fails to descend to equivalence classes [Lengyel 2026]. The present paper retains valid interpretation functors $F_M:S_T\to\mathbf{Pfn}$ and $G_M:\mathcal B_T\to\mathbf{Set}$, where $\mathcal B_T=\operatorname{Tot}(\operatorname{Split}(S_T))$. Their soundness factorizations relate the internal deductive structure to validity. The comparison and lifting hypotheses then support the essential-incompleteness conclusions. Keeping the $S_T$ application makes this mathematical difference explicit; the Miller and cosheaf constructions supply further representation results.

## Length and next revision

No shortened page count is established. Consolidation preserves every current application and removes repeated arguments; its saving must be measured by rebuilding the manuscript. The earlier page estimates based on moving Miller or the cosheaf construction no longer describe the recommended scope.

The next revision should merge the numerical foundations as specified above, replace the repeated proofs in Appendix B and §9 by references, and remove the preliminary arithmetic instance at the end of §5.4. It should retain all hypotheses, arrow types, naturality arguments and arbitrary-algebra fold proofs. The final abstract and introduction remain deferred: their present Miller-first roadmap and all-model description need to follow the final result order and soundness route. The application summary at the end of §4 should be checked at the same time.

After consolidation, compile the exact source, check references and diagrams, measure the resulting length, and rerun the mathematical and writing reviews on the changed passages. This audit has not yet carried out those manuscript changes.

## Literature supporting the scope decision

A. Heller, “An existence theorem for recursion categories,” *Journal of Symbolic Logic* **55** (1990), 1252–1268, [doi:10.2307/2274486](https://doi.org/10.2307/2274486). The publisher's introduction extract verifies the quoted motivation and its contrast with number-based examples. This supports retaining the categorically distinct representation example. This audit did not undertake a new general literature search.

F. Lengyel, *Pointwise provable equality and the failure of composition* (2026), [arXiv:2609.25556](https://doi.org/10.48550/arXiv.2609.25556). This supplies the obstruction to using the pointwise systems as categorical targets; it does not obstruct the valid uniformly provable syntactic category.

## Writing source and audit limits

The Mathematical Writing review consulted the supplied Knuth–Larrabee–Roberts text, especially §1, items10–15 and26, and §§4–5. Its guidance supports connected exposition, definitions at the point of need, consistent notation and removal of unnecessary jargon. The one-purpose requirement and the choice of which application to retain are the author's criterion and editorial judgments, rather than rules attributed to that source. The full source-grounded review is included in the repository audit record.

The complete assembled source was covered by the review team. The audit checked the dependencies relevant to proposed consolidation and movement; it did not re-prove every theorem or reverify the literature. No cuts, new proofs, Lean changes, or manuscript repagination were performed. The next implementation task is to consolidate the confirmed repeated proofs while retaining the cosheaf construction, then rebuild and measure the result. Any separately adopted scope change must preserve its full proof package and update the advertised claims. The mathematical and writing reviews should then be rerun on the changed text.
