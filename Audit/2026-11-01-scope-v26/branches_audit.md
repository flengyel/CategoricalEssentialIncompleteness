# Application and comparison branches in version 26

This report audits the mathematical roles and relocation dependencies of §8, §9, and Appendices B–D in *Logical consequence and essential incompleteness in recursion categories*, version 26, commit `490418a5eecbefa532e4d9283a7d504e4c611198`. The paper is 77 pages. No manuscript file was edited.

The principal conclusion is that the Miller, three-point, and faithful-family developments are independent branches of the current core argument. They are mathematical outcomes, not dispensable material merely because later results do not cite them. Moving their full treatments can reduce the scope of the main paper. It also changes which applications and representation results the main paper itself establishes.

## Recommendation

For the immediate length problem, retain the current general comparison, internal theory, syntactic realization, soundness, and arithmetic development with Appendix A, and move the full Miller application, the complete three-point construction, and Appendix D to companion treatments. Keep the section-lifting counterexample close to the comparison theorem. The first three moves account for about 23 existing pages and leave roughly 54 pages; this is a scope estimate, not a compiled shorter manuscript.

If the main paper must contain one complete example beyond numerical carriers and syntactic arithmetic, retain the three-point construction rather than Miller. It explicitly proves a restriction-category non-equivalence with ordinary recursion and realizes logical consequence in a category whose universal object has no decidable internal equality. Miller is shorter and has a striking separation phenomenon, but the current text does not prove the analogous non-equivalence theorem for its category. Retaining the full three-point branch while moving Miller and Appendix D leaves roughly 68 pages before limited consolidation. There is no evidence for promising a 30-page manuscript while retaining the present core and a complete such application.

This recommendation concerns the paper's purpose and length. It does not decide whether an application is novel or worthy of a separate paper.

## Current branches and their mathematical roles

| Branch | Existing pages | Mathematical output | Dependence on the core |
| --- | --- | --- | --- |
| §8, Miller sequences | Approximately 42–48, about 6 pages because boundary pages are shared | A recursion category of computations with domain and value independent of a representation; an inseparable pair whose image is separable after fixing a representation; a consistent, essentially incomplete theory of real closed fields in that computability class | Uses the categorical lifting theorem, domain-incompleteness corollary, and the first-order syntax/theory construction of Appendix A |
| §9 and Appendix B, three-point construction | Approximately 48–55 and 64–71, about 14 pages because boundary pages are shared | A recursion category not restriction-equivalent to ordinary recursion, its completed logical objects, internal inseparability, effective endpoint observations, and essentially incomplete propositional endpoint theories | Uses the numerical category and partial-map comparison, the lifting and incompleteness theorems, the propositional part of Appendix A, and `Pair(Rec)` from §7.6 |
| Appendix C | Approximately 71–74, about 3 pages | A faithful range functor with all other target conditions for which lifting and the source inseparability conclusion fail; disjoint-domain arrows need not have an upper bound | Shows the necessity of a hypothesis of the central lifting theorem and is referenced from §3 |
| Appendix D | Approximately 74–76, about 3 pages | Faithful all-model interpretation, ambient-theory extension comparison, numeral observations, and a complete ambient theory showing that internal inseparability alone does not imply ambient logical incompleteness | Uses the syntactic category, individual model interpretations, the finite switch, and the lifting theorem; it is not required by the one-model soundness/ultrapower argument |

Page estimates cannot be added as disjoint integer page ranges: §8 begins on page 42, §9 on page 48, Appendix A on page 55, Appendix B on page 64, Appendix C on page 71, and Appendix D on page 74.

## Result inventory and consumers

The table records semantic consumers as well as explicit cross-references. A theorem can be a branch's terminal purpose even if it has no later consumer. Source line anchors refer to the current version-26 modular sources.

### Miller branch

| Result and anchor | Role and consumers | Proposed location |
| --- | --- | --- |
| Lemma 8.1, `lem:miller-unanimity`, §8 source line 47 | The uniform compactness search constructs the operation used as the Turing morphism in Proposition 8.2; it also supplies the diagonal-pair interpretation used by the reduction | Miller companion |
| Proposition 8.2, `prop:miller-category`, line 97 | Establishes the recursion-category structure, ranges, weak choice, local connectedness and Turing universality; the subsequent lifting application and the total splitting use this structure | Miller companion |
| Lemma 8.3, `lem:miller-cut-reduction`, line 196 | Gives the ordinary recursive map reducing the diagonal pair to the below/above-half sets; its map is used in Corollary 8.4 even though the proof does not cite the lemma label | Miller companion |
| Corollary 8.4, `cor:miller-cuts-inseparable`, line 273 | Supplies the inseparable input pair for Theorem 8.6; its second assertion gives a separator for every fixed representation and supports the subsequent failure of Turing-morphism preservation | Miller companion |
| Proposition 8.5, `prop:miller-theory-realization`, line 320 | Establishes regularity, monomorphism inverses, and parameterized syntax/list and derivation initiality for the Miller category; required for the logical consequence object in Theorem 8.6 | Miller companion, with its realization proof retained |
| Theorem 8.6, `thm:miller-incompleteness`, line 441 | The terminal logical application: every consistent extension with the same semidecidable axiom condition is incomplete | Miller companion |

The unnumbered `J_p:E_a→Rec^p` comparison, the split target `K_p`, and the argument that `J_p(tau_a)` is not Turing are an additional mathematical comparison in this branch. The domain/value independence condition must be retained; using a separate program for every representation would change the category and its theorem. The ordinary-recursive reduction in Lemma 8.3 is also stronger than a reduction relative to one chosen representation and must not be weakened to shorten the argument.

The initial-algebra proof in Proposition 8.5 is not redundant merely because the numerical case is proved in Proposition 7.7. It must establish that evaluation has the same domain and value for every representation, even though search witnesses may vary. A common coding or evaluation lemma might later organize both proofs, but such a lemma is not supplied by the present manuscript and must not be assumed in a length reduction.

### Three-point branch

| Result and anchor | Role and consumers | Proposed location |
| --- | --- | --- |
| Proposition 9.1, `prop:endpoint`, §9 source line 194 | Evaluation preserves partial-map structure and the two endpoint Turing morphisms remain universal; used for recursive inseparability of the endpoint diagonal domains and the effective observation theorem | Three-point companion |
| Proposition 9.2, `prop:fork-syntax-initial`, line 357 | Characterizes the formula object by initiality in the functor category; part of the representation claim and prerequisite for applying the propositional construction of Appendix A | Three-point companion |
| Proposition 9.3, `prop:fork-proof-initial`, line 476 | Gives initiality of the inference algebra; directly used in Theorem 9.4 | Three-point companion |
| Theorem 9.4, `thm:fork-proof-presentation`, line 507 | Identifies the least theorem subfunctor, proves component consistency, and gives the atomic restriction inequalities; used in Theorem 9.5 | Three-point companion |
| Theorem 9.5, `thm:cosheaf-observation`, line 562 | Applies the internal incompleteness criterion and proves recursive inseparability of effective endpoint observations; includes a functor to `Pair(Rec)` | Three-point companion |
| Corollary 9.6, `cor:cosheaf-essential-incompleteness`, line 606 | Terminal statement for ordinary c.e. extensions of each endpoint propositional theory | Three-point companion |
| Proposition B.1, `prop:fork-cosheaves`, Appendix B line 9 | Establishes the topology/functor-category interpretation; required for the term “cosheaf construction,” though the partial computational functor category can be defined without it | Three-point companion |
| Proposition B.2, `prop:fork-total`, line 79 | Proves finite limits, extensive coproducts, regularity, componentwise monomorphisms and images; supplies hypotheses for B.3 and the least-theorem-image construction | Three-point companion |
| Proposition B.3, `prop:fork-structure`, line 154 | Constructs the partial category, restriction/range/join calculus and weak choice; used throughout §9 and the subsequent recursion-category construction | Three-point companion |
| Proposition B.4, `prop:fork-local`, line 241 | Gives local connectedness, needed by the lifting theorem in §9.1 | Three-point companion |
| Lemma B.5, `lem:fork-dominance`, line 276 | Gives the universal-object embedding; used for essential surjectivity of the restriction splitting and the Karoubi comparison | Three-point companion |
| Lemma B.6, `lem:fork-frames`, line 329 | Gives chosen product, coproduct and word isomorphisms; proves the selected generated subcategory is isotypical and supplies its parity coproduct map | Three-point companion |
| Theorem B.7, `thm:fork-turing`, line 388 | Constructs the actual compatible Turing morphism, with equality of domains and values; required by B.8 and the endpoint computations | Three-point companion, proof retained |
| Proposition B.8, `prop:fork-recursion`, line 527 | Establishes the recursion category and equivalence of its restriction splitting with the full partial functor category; needed to say that the logical objects live in a completion of the given recursion category | Three-point companion |
| Corollary B.9, `cor:fork-karoubi`, line 574 | Gives the additional Karoubi-envelope representation; not required for the incompleteness argument if that argument is stated only in the restriction splitting | Three-point companion; optional scope refinement if the completion claim is narrowed |
| Proposition B.10, `prop:fork-distinction`, line 653 | Proves genuine non-equivalence with ordinary recursion and failure of decidable equality on the universal object; a terminal representation/comparison result supporting why this example matters | Three-point companion, not deletion as “unused” |

The unnumbered numerical equivalence `Q_num:Split(Rec)→Par(C_rec,Mono)` in Appendix B, lines 609–646, is required by the current presentation of endpoint functors. The unnumbered probe functors `Phi_i` and their natural isomorphisms with underlying endpoint evaluation, §9 lines 230–260, explain the observation interpretation; the final theorem uses the resulting probe-domain notation. The central component's failure to preserve the Turing morphism's universality, lines 263–274, is a further boundary comparison. It is independent of the two endpoint universality results and must not be described as their consequence.

### Lifting counterexample and all-model comparison

| Result or construction and anchor | Role and consumers | Proposed location |
| --- | --- | --- |
| Proposition C.1, `prop:missing-lift`, Appendix C line 47 | Verifies the failure of the central lifting conclusion with its hypothesis omitted, including an explicit nonrecursive section and disjoint-domain arrows with no common upper bound; §3 line 229 refers to the appendix to explain the theorem's hypothesis | Retain near the comparison theorem, possibly as its appendix |
| Theorem D.1, `thm:faithful`, Appendix D line 25 | Constructs the faithful all-model functor and verifies target properties; directly consumed by Corollary D.2 | Separate comparison treatment |
| Theory-extension square, Appendix D lines 65–91 | Shows quotient functors commute with family projection and preserve the relevant program operations; used by the extension assertion of D.2 | Same comparison treatment |
| Corollary D.2, `cor:pair`, line 95 | Applies the lifting theorem to all-model interpretations and transports the specified pair through ambient theory extension | Same comparison treatment |
| Failure of target Turing universality, lines 125–143 | Distinguishes source universality from the size of the all-model target; clarifies the limits of the functor | Same comparison treatment |
| Numeral observations and faithfulness identity, lines 145–165 | Compares provability of each numeral instance, constant arrows, and their faithful family images | Same comparison treatment |
| Complete ambient theory, lines 167–183 | Shows that internal computational inseparability does not by itself imply logical incompleteness of the ambient theory; a substantive distinction, not empty reassurance | Preserve in the comparison treatment or retain a precise stated limitation in the main paper if that misconception is otherwise invited |

## Incoming uses outside each branch

I searched every modular `.tex` source for `ref`, `eqref`, and `autoref` commands naming labels defined in these files, and then checked the semantic uses in the actual proofs.

1. §8's labels are used only within §8 and the deferred introduction. No §2–§7 proof or Appendix A construction needs a Miller result.
2. §9 and Appendix B form one package with references in both directions. Their labels are used only in that package and the deferred introduction. Neither is a prerequisite of the current arithmetic chain.
3. Appendix D's labels have no incoming proof references from the current main sections or Appendix A. `sec:family` occurs in the deferred introduction's roadmap. The standard-code soundness proof and ultrapower comparison in §6 do not use the all-model family.
4. Appendix C differs: §3 line 229 explicitly points to it to substantiate the necessity of lifting. It remains optional for proving the positive comparison theorem, but it supports a mathematical boundary claim made in the core exposition.

Zero incoming references do not establish that a result is useless. Propositions 8.2, 9.2, B.4, and Theorem 9.4, for example, have semantic consumers even where a later argument does not repeat their labels. Terminal results such as 8.6, 9.6, B.10, and D's complete-ambient-theory example are purposes of branches, not abandoned intermediate lemmas.

## Exact dependency packages if material moves

### Miller treatment

Retain all of §8, including the representation space and its compactness, the source category, uniform domain/value condition, both target functors, diagonal pair, reduction, separator comparison, total splitting, first-order syntax/list/derivation realization, and the real-closed-field axiom presentation. It also needs:

- the restriction/category/range and Turing-morphism definitions used in §2;
- the precise hypotheses and conclusion of Theorem 3.5, with its underlying comparison and local-section lemmas if a proof is included;
- the inclusion-into-splitting argument preserving inseparability;
- Corollary 4.3 with its total inverse-image join hypothesis;
- the first-order syntax, admissible substitution, inference rules, image/leastness theorem, and range/regular-image interface from Appendix A;
- the existing Miller 2004 and Bauer–Hanson references with their specific roles and the ordered-field calculus/axiomatization dependencies.

A companion that merely says “apply the main construction” would be incomplete at the user's stated standard. It must include the needed formal statements and either give their proofs or cite a stable scholarly source containing them with matching hypotheses. If the companion is to be self-contained as a construction document, its necessary Appendix A material must accompany it. Moving six existing pages therefore does not mean that the finished independent document will be six pages.

### Three-point treatment

Move §9 and Appendix B together. The main section currently fixes X, J, the numerical category, sequence encodings, V, and the generated subcategory before Appendix B uses those choices; moving only the appendix strands definitions. The package also needs:

- the numerical category `C_rec`, its regularity/extensivity and mono/partial-inverse properties;
- the partial-map category, restriction splitting and the numerical equivalence currently proved in Proposition 7.7 and repeated in Appendix B;
- the comparison/lifting theorem and the domain-incompleteness corollary, including exact target and total inverse-image hypotheses;
- the propositional construction of Appendix A.6, the general rule endofunctor of A.4, Theorem A.5, and Lemma A.7;
- the definition and morphisms of `Pair(Rec)` from §7.6, since Theorem 9.5 explicitly has that category as its target;
- the numerical program/specialization conventions and their exact simultaneous-definedness equations;
- the Curry cosheaf and Heller recursion/frame references used for the topology and categorical construction.

It does not require the full first-order quantifier/substitution construction, the S_PA soundness argument, the indexed family, or the uniform independent-sentence theorem for its existing propositional conclusion. It must preserve its own direct formula/proof initiality and consistency proofs. In particular, the universal object lacks decidable equality, so one cannot replace these proofs by an unverified application of the first-order realization hypotheses.

### All-model comparison

Move Appendix D with the typed S_T/program quotient definitions, the individual model functors and graph-preservation theorem, the finite-switch lemma, and the comparison theorem. The numeral-observation construction needs the arithmetized composition and constant-program equations. The complete-ambient-theory example needs the ordinary numerical category and standard graph interpretation. The completeness and downward Löwenheim–Skolem uses remain explicit. The newer one-model standard-code soundness and ultrapower argument need not be copied merely to explain this branch.

## Consolidation possible without changing scope

These changes would remove repeated proof, not shorten a required universal property into an unexplained phrase:

| Anchor | Overlap | Safe consolidation |
| --- | --- | --- |
| Appendix B lines 89–116 versus Proposition 7.7 | Numerical finite limits, image factorization, computable preimage descent, and pullback stability are proved again before transfer to the functor category | Cite Proposition 7.7 for the numerical base and retain the componentwise descent/naturality proof for E; the latter is new |
| Appendix B lines 609–646 versus Proposition 7.7's partial-map equivalence | Another numerical coding equivalence is constructed in the reverse direction to the named equivalence used in §7.4 | Reuse an explicitly named quasi-inverse or comparison from §7.4, with its direction and object/arrow actions recorded; do not equate two unchosen presentations |
| §9 lines 145–157 versus Proposition B.4 | The local-connectedness argument using finite singleton-generated subfunctors is repeated | State the needed local-connectedness conclusion in §9 and cite B.4 for the proof |
| §9 lines 162–170 versus Proposition B.10 | The five-versus-two terminal-subobject argument is summarized in the main section and proved in the appendix | Keep a short statement of the distinction and its significance, citing B.10; retain the full proof once |

These are limited savings. They do not account for the approximately twenty pages occupied by the two application branches.

Two further possible reductions are genuine changes of scope and require corresponding statement changes:

- The free nonempty-word semigroup construction and the word frame in Appendix B are beyond the recursion-category definition currently adopted in §2.3, which requires prodominicality, isotypicality, binary products, and a Turing morphism. The chosen R_X is nevertheless explicitly closed under nonempty-word formation. Removing the word construction would require changing that generated subcategory and the stated frame result; it cannot be done while retaining those claims verbatim.
- B.9's Karoubi comparison is stronger than the restriction-splitting comparison sufficient for the existing logical objects. It can move with the completion discussion, but the initial §9 claim about objects in Kar(R_X) must then be restated using Split(R_X) if B.9 is omitted from that treatment.

## Choosing one application

The three-point construction is the stronger test of a claim about representation in recursion categories beyond a numerical presentation: B.10 proves the categorical distinction, and the propositional realization works despite lack of decidable equality on V. Its cost is the substantial compatible Turing-morphism and completion construction in Appendix B. Those proofs carry the distinction and cannot be discarded while citing only the numerical case.

Miller gives more first-order logical content in fewer pages: real closed fields, constants carrying a noncomputable sequence, and an incompleteness theorem relative to a representation-independent computability class. It also shows that a faithful range functor preserving products may send an inseparable pair to a separable one when it does not preserve the relevant Turing universal property. This is a different mathematical contribution from B.10. It should be the selected application if that phenomenon or the real-closed-field theorem is the announced principal outcome, as the deferred version-26 introduction still says.

For a main paper centered on categorical logical consequence, syntax realization, soundness comparison, and uniform arithmetic independence, neither branch is a prerequisite. My preferred shorter main paper moves both full branches and Appendix D, with precise companion-result descriptions only if the introduction needs them. If the author chooses to make a full nonnumerical representation example an essential main result, retain the three-point branch and accept the longer paper. These are scope choices; a deletion based solely on page count would not preserve the same paper.

## Source and review scope

I read §8, §9, and Appendices B–D completely, plus the relevant §2 recursion-category definition, comparison statement, current introduction claims, Appendix A result labels, and numerical realization interfaces. I inspected `main.aux` for result numbers and page locations and searched incoming references across all modular sources. I consulted the supplied Knuth–Larrabee–Roberts *Mathematical Writing*, §1, especially points 5 and 10–17 concerning self-contained statements, connected explanations, reader expectations, and notation. Those support preserving proof interfaces and meaningful exposition; the choice of main-paper scope above is independent editorial judgment under the author's one-purpose requirement.

This is a dependency and length audit, not a new correctness review of every branch theorem, a novelty assessment, literature search, or Lean verification. No external literature claim was added, and no manuscript source was changed.

## Addendum: retain the complete cosheaf example in the main paper

The author has now required that the cosheaf construction remain in the main paper. This constraint supersedes the earlier recommendation to move §9 and Appendix B. Their non-equivalence result, failure of decidable equality on the universal object, and internal propositional consequence construction directly support the intended categorical contribution.

The revised recommendation is to preserve that complete branch and its dependencies, consolidate genuine repetition, and separate the independent all-model and numerical-first-order comparisons. Moving Miller remains a separate optional scope choice.

### Retained numerical foundation versus the independent numerical logical case

The cosheaf example uses `C_rec` and its partial-map presentation as its numerical base. It does not use the first-order syntax/list initiality theorem for `C_rec`, the numerical-versus-syntactic first-order proof-code bijection, or the independently realized arithmetic incompleteness proof. Its propositional formula and derivation initiality are proved directly in Propositions 9.2–9.3, and its logical application uses Appendix A.4/A.6 and Corollary 4.3.

The following extraction preserves the existing dependencies. These are proposed boundaries in the version-26 sources, not edits already made.

| Existing block | Proposed treatment | Reason |
| --- | --- | --- |
| `08c-numerical-realization.tex` lines 4–35 | Keep: `Rec`, `C_rec`, carrier notation, tuple codings | Needed for the numerical components, encoded carriers, endpoint comparison, and non-equivalence invariant |
| Proposition 7.7 structural statements, lines 39–51, and proof lines 63–210 | Keep as a numerical-base proposition, with a title and statement restricted to these conclusions | Supplies the total equivalence, regularity/extensivity, partial inverses of monomorphisms and partial-map equivalence used by the cosheaf construction |
| Proposition 7.7 first-order claims, lines 53–60, and proof lines 212–393 | Move as the numerical first-order realization theorem with its full typed proof | The cosheaf branch has its own propositional realization and does not invoke these first-order universal properties |
| Arithmetic sentence objects and proof-code comparison, lines 396–515 | Move with that numerical realization | These construct `Prf_T`, the numerical arithmetic theory image, the `rho_n/eta_n/rho_T` comparisons, and transported negation/substitution for the separate numerical arithmetic application |
| `08d-numerical-incompleteness.tex` | Move its diagonal/arithmetic proof, retaining the few numerical-base declarations identified below | The syntactic arithmetic proof and uniform theorem are already in §§7.1–7.3; the cosheaf endpoint inseparability argument applies the general lifting theorem directly to its own endpoint evaluator |
| §7.6 arithmetic observation sets and functor, parent arithmetic source lines 290–299 and 306–314; Bernardi comparison, lines 320–331 | Move with the numerical arithmetic case | These depend on the numerical `theta`, `nu`, `t_T`, `A`, and `B` moved above |
| `Pair(Rec)` definition, parent arithmetic source lines 300–306 | Keep and relocate with the numerical foundation or immediately before the endpoint observation theorem | Theorem 9.5 explicitly has this category as its target; retaining only the arithmetic observation application elsewhere would strand the definition |

Also retain the ordinary numerical Turing-morphism statement and its specialization justification (`08d`, lines 11–14), and the definition and preservation properties of `J_rec:Rec→Pfn` (lines 28–31), beside the retained numerical-base definitions. Appendix B's numerical comparison currently names `J_rec`, and the distinction theorem compares with the recursion category of ordinary partial recursive functions. The first-order logical apparatus is not needed to supply either declaration.

This extraction narrows the main paper's own proved realization claim: it would no longer prove the full first-order realization of Appendix A in `Tot(Split(Rec))` or give its separate numerical arithmetic derivation. It preserves the syntactic realization in `B_PA`, the main arithmetic and uniform-independence results, and the cosheaf propositional realization. If a main claim is to include all three full realizations as established results, the numerical first-order theorem cannot simply disappear; it must remain or be supplied through a precise, stable companion result. The purpose of this proposal is to separate an independent case, not to imply that its proof has become unnecessary for that case.

### All-model comparison and its source switch

Move Appendix D together with the subsection **§6.1, “Lifting complementary conditionals,”** source lines 58–123 of `06-interpretation-in-models.tex`. That subsection contains Lemma 6.2 (`lem:switch`) and Corollary 6.3 (`cor:model-pair`). The only references to these labels are within that subsection and Appendix D. The current arithmetic comparison and uniform proof use the functional-search construction directly, not this all-source-complementary-pair corollary.

Retain Proposition 6.1 (`prop:model`) and its preceding definition, source lines 3–56. They construct the individual interpretation functors required by the current total interpretation, soundness, and ultrapower argument. Moving §6.1 is not a reason to move those definitions or Proposition 6.4 on the total regular interpretation. The all-model comparison remains a substantive independent result, and the complete-ambient-theory example should accompany it.

### Consolidation with the cosheaf branch retained

The safe consolidations listed earlier now become primary cuts: Appendix B should cite the retained numerical-base proposition for numerical regularity rather than reprove it, and its numerical partial-map comparison should reuse the named equivalence with the required inverse direction and code comparisons. Keep the genuinely new proof that componentwise descent is natural in the functor category. In §9, state local connectedness and the terminal-subobject distinction with precise references to B.4 and B.10, retaining each proof once. None of these moves permits suppressing the compatible Turing-morphism proof, formula/proof initiality, or consistency argument.

The numerical logical and arithmetic blocks proposed for relocation occupy roughly four to five existing pages after preserving the numerical foundation and `Pair(Rec)`. Appendix D and §6.1 together occupy roughly three to four pages. The literal repeated numerical-base and cosheaf-summary arguments offer smaller savings, around a page rather than another large branch. These are approximate existing-block estimates; the revised boundaries have not been compiled. Keeping Miller as well as the cosheaf branch would therefore leave a paper around the high sixties after these moves. Moving the approximately six-page Miller treatment as an additional scope choice could bring it into the low sixties. A much shorter paper cannot be promised from these blocks alone.

## Latest-scope addendum: retain every application and combine numerical foundations once

The author's latest instruction supersedes all preceding relocation recommendations. Retain the syntactic category `S_T`, the numerical realization and arithmetic application, Miller's construction, the cosheaf construction, and the existing comparison applications. Miller's result is to remain as mathematical content in its own right, and `S_T` remains part of both the historical and mathematical development. Appendix D is not a selected cut. The recommendation is now consolidation of repeated foundations and proofs, preserving every application and every result presently asserted. The earlier high-sixties and low-sixties page estimates therefore do not describe the current recommendation.

### Which version of the common numerical foundations to retain

Use §7.4 as the single definition and proof of the numerical base. Its explicit distinction between objects and carriers is more suitable for the rest of the paper than the older raw-subset presentation in §9 and Appendix B. Import the useful explicit descent construction from Appendix B, and retain the functor-category arguments that are not repetitions.

| Item | Best existing source | Consolidation |
| --- | --- | --- |
| Objects, morphisms, equality and carrier notation | §7.4, `08c-numerical-realization.tex`, lines 18–35 | Retain objects `C=(m,C_0)`, carriers `|C|=C_0`, arrow `f:C→D`, represented function `|f|:|C|→|D|`, and the convention that `f(x)` abbreviates `|f|(x)`. Do not revert to writing a subset as though it were the same typed object. |
| Tuple coding, including dimension zero | §7.4, lines 29–35 | Retain the explicitly typed injections `κ_m:N^m→N`, recursive images `K_m`, inverses, `κ_0(())=0`, `K_0={0}`, and `κ_1=id_N`. Appendix B needs these choices, rather than another unchosen tuple injection. |
| Total equivalence | §7.4, lines 63–111 | Retain `Q:C_rec→B_rec`, `F:B_rec→C_rec`, their object/arrow actions and the typed natural isomorphisms `u:FQ⇒id_C` and `v:QF⇒id_B`. This supplies comparison data, not only an existence assertion. |
| Finite limits, tagged coproducts and numerical extensivity | §7.4, lines 113–137 | Retain the chosen dimensions, carriers and universal maps. Delete the repeated numerical finite-limit argument in B.2, lines 89–99; retain B.2's transfer to `E=C_rec^J` and its slice-equivalence argument. |
| Numerical regular images and descent | §7.4, lines 139–160, together with B.2, lines 100–116 | Keep the typed image object and factorization of §7.4. Express its preimage search as the section `s_q:D→C` described below, then give descent once. B.2 cites this numerical fact before proving natural descent componentwise. |
| Monomorphisms and partial inverses | §7.4, lines 162–177 | Retain the singleton test, injectivity criterion and typed `μ_m:Q(C)⇀Q(B)` with its two inverse equations. B.2 keeps its three functor-category probes `H_j`; its final numerical inverse-search sentence can instead cite this result. |
| Partial-map equivalence in the direction from spans | §7.4, lines 179–210 | Retain `tilde Q:Par(C_rec,Mono)→Split(Rec)`, with the action `Q(g)μ_m`, span invariance and the domain/value proof of composition and restriction preservation. |
| Partial-map equivalence in the reverse direction | Appendix B, lines 609–646 | Move its named `Q_num` into the same numerical foundation and state its action using the object/carrier convention of §7.4. Give the actual inverse comparison data once, as below; do not reprove a second unnamed existence of an equivalence in Appendix B. |
| Regularity of the functor category | B.2, lines 118–152 | Keep. Images must form subfunctors, descended component maps must be natural, and tag inverse images must form subfunctors. These are additional assertions, not repetitions of numerical regularity. |

For the shared descent proof, let `q:C→D` be a surjective morphism of `C_rec`. On an input `y∈|D|`, enumerate `|C|`, dovetail the computations of `q`, and select the first discovered `x` with `q(x)=y`. This computes a morphism

\[
 s_q:D\longrightarrow C,\qquad q s_q=1_D.
\]

For `h:C→Z` constant on the fibers of `q`, put `d=h s_q:D→Z`. Fiber constancy gives `dq=h`, and surjectivity of `q` gives uniqueness. This is exactly the common numerical computation, with its source, target and equation visible. A program for `s_q` may be partial outside `|D|`; as an arrow of `C_rec` it is total on its stated source carrier.

Do not apply this by asserting that a componentwise surjection of functors has a natural section. B.2 correctly proves naturality of the descended maps by cancellation. For `q:Y→Z` componentwise surjective and `u:Y→W` constant on its kernel pair, retain

\[
 r_i^W v_0 q_0=r_i^W u_0=u_i r_i^Y
 =v_i q_i r_i^Y=v_i r_i^Z q_0.
\]

Surjectivity of `q_0` yields `r_i^Wv_0=v_i r_i^Z`. This is the needed functor-category argument; choosing separate numerical sections supplies the component maps, but does not supply their naturality.

### One pair of explicitly typed partial comparison functors

Put `C=C_rec`, `S_rec=Split(Rec)` and `K=Par(C,Mono)`. Let `J_C:C→K` be the canonical inclusion of total maps, sending `g:C→D` to `[C←id_C C→g D]`. Keep the existing `tilde Q:K→S_rec` and define the opposite-direction functor from Appendix B beside it:

\[
 Q_{\mathrm{num}}:\mathscr S_{\mathrm{rec}}\longrightarrow\mathcal K.
\]

For `A=(X,e)` put `D_e=γ_X(dom e)` and

\[
 Q_{\mathrm{num}}(A)=F(A)=(1,D_e).
\]

For an arbitrary partial split arrow `f:A⇀B`, where `B=(Y,d)`, let

\[
 \widehat f=\gamma_Y f\gamma_X^{-1}|_{D_e}:D_e\rightharpoonup D_d,
 \qquad U_f=\operatorname{dom}(\widehat f)\subseteq D_e.
\]

Its image is the span

\[
 Q_{\mathrm{num}}(f)=
 [\, (1,D_e)\xleftarrow{i_f}(1,U_f)
                  \xrightarrow{g_f}(1,D_d)\,],
 \qquad |g_f|=\widehat f|_{U_f},
\]

where `i_f` is the inclusion. Here `U_f` is c.e., `(1,U_f)` is an object of `C`, and `g_f` is total on its stated source. This is the normalized-span form of Appendix B's construction. Its functor and restriction equations follow from the exact domains and values of the represented partial maps. On total arrows it agrees with `J_C F`.

The isomorphisms already displayed in §7.4 then have the following types in the partial categories:

\[
 J_C(u_C):Q_{\mathrm{num}}\widetilde Q(C)\xrightarrow{\cong}C
       \quad\text{in }\mathcal K,
 \qquad
 v_A:\widetilde Q Q_{\mathrm{num}}(A)\xrightarrow{\cong}A
       \quad\text{in }\mathscr S_{\mathrm{rec}}.
\]

State and prove naturality for arbitrary partial arrows, not only for the total arrows used in the present proof of `u` and `v`. For `a:C⇀D` in `K` and `f:A⇀B` in `S_rec`, the equations are

\[
 a\,J_C(u_C)=J_C(u_D)\,Q_{\mathrm{num}}\widetilde Q(a),
 \qquad
 f v_A=v_B\,\widetilde Q Q_{\mathrm{num}}(f).
\]

The decoding and encoding formulas identify both domains and values in each equation. This supplies natural isomorphisms in the full partial categories and proves that the two restriction functors are quasi-inverse. The present complete full/faithful/essentially-surjective argument for `tilde Q` and Appendix B's second such argument need not both remain after these explicit comparison data have been proved. The span invariance and composition argument should remain: those establish the asserted functor, rather than merely its action on a chosen representation.

If the notation `J_rec` is used in the displayed definition of `widehat f`, its definition currently in §7.5 must move up with the definition of `Rec`. Alternatively the formula above uses `f` itself, since §7.4 has already defined arrows of `Rec` to be the actual represented partial functions. Do not introduce a reference to the later `J_rec` before it is defined.

### Placement and effect on the applications

The least disruptive placement is the beginning of §7.4: define the numerical categories and codings once; prove their finite-limit, coproduct, image and mono properties; give the typed total and partial comparison functors and comparison isomorphisms; then continue with the existing first-order realization and proof-code comparison. The structural conclusions can be separated from the first-order realization into two propositions without moving either application out of the paper. The first proposition then becomes the reference used by Appendix B.

At the start of §9, replace the second definition of `C_rec` by the reference to this numerical foundation, and keep the new definitions of `J`, `E=C_rec^J`, its objects, component morphisms and natural transformations there. Update the old raw-carrier notation consistently: `Y_j` is an object of `C_rec`, elements belong to `|Y_j|`, and a c.e. subfunctor is specified by component objects and inclusion arrows whose carriers are the stated c.e. subsets. Similar object/carrier distinctions are needed for the components of the universal object. This prevents the later sections from silently changing the category's object convention after the shared definition has been selected.

In Appendix B, B.2 should cite the numerical proposition and prove its genuinely additional assertions about `E`; the later numerical comparison block should invoke the now earlier `Q_num` with its direction and codomain recalled. Its use by §9's endpoint-evaluation comparison is consequently defined before use, rather than being proved by a separate appendix construction. The categorical distinction theorem continues to use the full comparison and does not lose an argument.

Keep the first-order realization in §7.4, its numerical arithmetic application in §7.5, the definition of `Pair(Rec)` used by §9.5, the syntactic `S_T` application, Miller's uniform representation proof, and the cosheaf syntax/proof initiality and consistency proofs. The latter two realization arguments have additional uniformity or naturality obligations; ordinary numerical first-order initiality does not discharge them. They are not numerical-foundation duplicates.

The other genuine repetition remains as identified above: the finite-probe local-connectedness proof and the five-versus-two subobject computation should each have one full proof in Appendix B, with the needed statements and precise references in §9. These consolidations preserve all present applications and mathematical claims. They offer modest savings, approximately a page of existing repeated argument before recompilation, not the large reductions associated with the now superseded scope proposals. No manuscript source has been changed.
