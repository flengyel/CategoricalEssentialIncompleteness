# Internal repetition in version 30: syntax, lists, and derivations

## Diagnosis

The broad alleged duplication is not present. Appendix A supplies a generic categorical construction **under existence hypotheses**; §§5, 7.4, 8, and 9 prove that particular categories and particular coded objects satisfy those hypotheses. Their repeated use of induction on finite trees does not make their conclusions interchangeable. Keep Appendix A self-contained, and keep the realization arguments where they are applied.

There is a small, definite avoidable replay in the numerical realization's identification of its free-variable and substitution algorithms (§7.4, `08c-numerical-realization.tex:404–417`). The same codes and algorithms have already been verified in PA in §5.3. Another exact induction is repeated between Appendix A and the last paragraph of Proposition 5.7, but the latter's explicit PA-provability claim explains why an unsupported cross-reference would be insufficient. A precise reference through \(\mathcal B_{\mathrm{PA}}\) would preserve that claim. These are local consolidations, not reasons to shorten all realization proofs or to reorganize the paper.

No manuscript edits were made.

## Reviewed outline and the job of each part

The paper is *Logical consequence and essential incompleteness in recursion categories*, version 30 (`preamble.tex`, PDF metadata). Section numbering below is confirmed by the current `main.aux`; file line references are to the current source.

| Part | Existing function and main prerequisite/result |
|---|---|
| §5.1, `05a:1–276` | Presents \(\mathcal B_T=\operatorname{Tot}(\operatorname{Split}(S_T))\) by \(\Sigma_1\) predicates; proves regularity, extensive finite coproducts, image formula, and partial inverses of monomorphisms. |
| §5.2, `05a:278–504` | Establishes canonical sequence/tree codes; proves finite membership is \(\Sigma_1\); proves **T-provable** initiality of syntax and lists in every parameter slice (Propositions 5.5–5.6). |
| §5.3, `05a:506–618` | Gives primitive-recursive implementations, proves their equations and carrier preservation in PA, and identifies them with Appendix A's categorical folds (Proposition 5.7). |
| §5.4, `05a:621–878` | Constructs finite derivations as \(\Sigma_1\) objects with a **T-provably total** universal fold (Lemma 5.8), then applies Appendix A to obtain the generated theory and its restriction idempotent. |
| §7.4, `08c:1–276` | Gives the numerical category \(\mathcal C_{\mathrm{rec}}\), its regular/extensive structure, its equivalence with the total restriction splitting, and the partial-map equivalence. This is the numerical foundation later used in §9. |
| Proposition 7.8, `08c:278–474` | Proves initiality for syntax/lists/derivations against **all numerical computable algebras**, including those whose totality is not PA-provable. |
| §7.4 after Proposition 7.8, `08c:476–595` | Compares numerical and syntactic rule labels and derivation carriers; obtains the precise conclusion-preserving bijection and numerical theorem range. |
| Proposition 8.5, `04:321–424` | Proves the categorical structure and realization in \(\mathcal D_a\), including common domain/value across all binary representations of the Miller sequence. |
| §9.3, `09:354–527` | Builds propositional syntax and derivations in \(\mathcal E=\mathcal C_{\mathrm{rec}}^J\); proves the component folds are natural under relabeling. Theorem 9.4 then applies Appendix A's image theorem. |
| Appendix A.1–A.3, `a:10–414` | States the categorical hypotheses and parameter stability; constructs Boolean/list/free-variable/substitution structure from the assumed initial algebras; proves categorical substitution identities. |
| Appendix A.4, `a:416–510` | Defines the inference endofunctor and proves that the image of an **assumed** initial derivation algebra is the least closed subobject (Theorem A.5). |
| Appendix A.5–A.6, `a:512–711` | Supplies first-order and propositional rule data, obtains sentence theories, and relates regular images to ranges. |
| §9 setup and Appendix B, `09:96–125`, `b:274–341` | Defines nonempty words, extends word formation to partial maps, proves the free-semigroup property, and constructs the specific natural frame isomorphism \(V\cong V^\#\). |

Appendix A therefore has one coherent job: construct logical consequence from the specified categorical data. It does not build numerical tree codes, establish a \(\Sigma_1\) presentation, or prove computability/naturality/representation independence of a concrete universal fold.

## Source principles actually checked

Read the supplied Knuth–Larrabee–Roberts *Mathematical Writing*, §1 and §§4–5, from `tmp/review_sources/klr.txt`. Section 1, point 5 favors self-contained theorem statements; points 10–11 favor connected explanation and complementary restatement, rather than a mechanical ban on saying something twice; point 12 asks what the reader knows at the point of use. Section 4 (printed p. 9) treats the placement of definitions as contextual; §5 (printed pp. 12–13) asks for nearby definitions, clear prose, and useful signposts. The following distinction between identical proof obligations and category-specific verification is this review's editorial application, not a quoted rule of KLR.

Read the attached Cockett paper's introductory account and §2, especially Definition 2.3 and Definition 2.4 (printed p. 7). Cockett explicitly distinguishes ordinary recursive objects from parameterized recursion and formulates the latter through the functor into a slice. That supports retaining the manuscript's parameter-slice checks. His generic list theory does not establish, without a realization argument, the manuscript's PA-provable graph equalities, invariance under Miller representations, or naturality of fork components. His introduction also distinguishes list arithmetic from regularity: it is not a replacement for the separate image/regularity hypotheses in Appendix A.

## Exact local repeats and minimally sufficient repairs

### 1. Definite avoidable replay: numerical free variables and substitution

**Locations.** Proposition 5.7, `05a:527–590`, versus Proposition 7.8, `08c:394–417` (PDF Proposition 5.7 begins p. 18; Proposition 7.8 begins p. 38).

**Repeated steps.**

1. The free-variable traversal concatenates children's lists and deletes the bound variable at a quantifier (`05a:539–550`; replayed at `08c:404–406`).
2. At a quantifier, substitution tests equality of variable names and the same two finite-membership conditions (`05a:564–579`; replayed at `08c:407–412`).
3. Other constructors have their term/atomic/connective equations (`05a:557–562`; replayed at `08c:413–414`).
4. Tree induction verifies those equations, then uniqueness of the parameterized folds identifies the algorithms (`05a:584–590`; replayed at `08c:415–417`).

**Why this one can be consolidated.** Unlike an arbitrary numerical algebra, these are the *same particular primitive-recursive algorithms on the same codes*. The numerical proof says so at `08c:394–396`. The PA proofs of their equations are already available, and evaluating those proofs in \(\mathbb N\) supplies the numerical equations. The numerical parameterized initiality proved in the current proposition supplies the uniqueness step. No new tree induction is needed here.

**Strongest necessity countercase.** Simply deleting the entire paragraph would remove the identification with Appendix A, which is needed to identify admissibility and the sentence object. It is also necessary to retain the displayed types at `08c:398–402`, the \(\operatorname{Adm}\) pullback and induced map at `08c:418–420`, and the concrete sentence carrier at `08c:420–422`.

**Minimal replacement for `08c:404–417`.**

> The carrier preservation and constructor equations proved in PA in Proposition~\ref{prop:st-substitution-realization} hold for these same algorithms in \(\mathbb N\). By the parameterized initiality just established, these numerical morphisms are the free-variable and substitution folds of Appendix~\ref{app:syntax-theories}. In particular,

Continue with the existing admissibility and sentence descriptions. This consolidates one replay while preserving the local realization and all its consequences.

### 2. Same induction twice, with a real PA-status obligation

**Locations.** Appendix A.3, `a:390–414`, especially `a:406–414`, versus the final paragraph of Proposition 5.7, `05a:608–617`.

**Repeated steps.** Both prove identity substitution and substitution at an absent variable by simultaneous term/formula induction. At a quantifier they make exactly the same split: equal names return the original formula; different names make identity substitution pass the capture test using \(\operatorname{FV}(\eta x)=[x]\); deletion transfers absence to the body; the induction hypothesis gives a successful unchanged result.

**Why retaining the present paragraph is defensible.** Proposition 5.7 promises that its source-restricted equations are provable in **PA**, whereas equality of the identified folds in an arbitrary \(\mathcal B_T\) yields only **T-provability**. Merely saying “this follows from the appendix” after discussing \(\mathcal B_T\) conceals that difference. This is a genuine duplication of induction, but it is short and has a useful proof-status purpose. It is not a mathematical defect.

**Safe optional consolidation.** After the algorithm/fold identification at `05a:589–590`, replace `05a:608–617` by:

> Regard the chosen \(\Sigma_1\) carrier formulas \(V,\Sigma_k,\Pi_k\) as objects of \(\mathcal P_{\mathrm{PA}}\), and form the same coded syntax and list predicates there. The preceding carrier and constructor-equation proofs identify the algorithms with the corresponding folds in \(\mathcal B_{\mathrm{PA}}\). Applying the identity and absent-variable substitution identities of Appendix~\ref{app:substitution} in that category gives their source-restricted graph equations as theorems of PA.

This explicitly instantiates the categorical construction using the **predicate counterparts** in \(\mathcal B_{\mathrm{PA}}\), rather than trying to lift arbitrary original \(\mathcal B_T\) objects or morphisms. Every chosen \(\Sigma_1\) carrier formula is already an object of \(\mathcal P_{\mathrm{PA}}\) (`05a:14–16`); no PA proof of a T-specific representative's idempotence or totality is needed to introduce that counterpart. The code predicates and their constructor algebra depend only on those carrier formulas, and the preceding proofs are available at \(T=\mathrm{PA}\). Keep the appendix's induction in full so that the common construction remains self-contained. If a direct PA induction is preferred for the intended audience, keeping the present ten lines is reasonable.

The nearby assertion that PA proves the two list-membership identities (`05a:530–532`, compared with `a:241–245`) is analogous, but it is only a brief claim inside the required algorithm verification, not a second developed proof. It does not justify another editorial cut.

### 3. Tiny exact replay: functor laws for the fork inference endofunctor

**Locations.** Generic definition `a:444–450`; special-case definition `09:458–467`.

**Repeated step.** Define the map on a pullback by its two projections, take the coproduct with the identity on axioms, then infer identity/composition laws from pullback uniqueness. The latter is precisely the generic construction specialized to \(R_0=\operatorname{Ax}\), \(R_1=0\), \(R_2=S^2\).

**Necessity countercase.** The fork proof needs the concrete modus-ponens pullback, its conclusion, and the comparison identifying this \(\mathsf H\) with Appendix A's \(H\); these supply the objects used throughout the later derivation proof. The fact that the \(R_1=0\) summand disappears uses extensivity (`09:466–467`) and must remain.

**Minimal optional repair.** Keep `09:438–457` and the rule-data identification at `09:463–467`. Replace `09:458–462` with “This is the inference endofunctor of Appendix~\ref{app:closed-subobjects} for the following rule data.” This is a few lines, and leaving the present concrete definition for readability is also defensible. Do not remove the concrete pullback diagram or shorten the initiality proof on this basis.

## Similar-looking arguments that perform different jobs

| Comparison | Common-looking step | Distinct obligation; strongest countercase to deletion | Recommendation |
|---|---|---|---|
| Appendix A vs §5 syntax/list proofs (`a:155–223`, `05a:372–504`) | Initial algebra and parameterized recursion language | Appendix A **assumes** initiality; §5 constructs the fold as a \(\Sigma_1\) relation and proves totality, fiber preservation, and uniqueness **in T**. Without those, the arrows do not exist in the syntactic category. | Retain. |
| §5 vs §7.4 syntax/list initiality (`05a:394–470,491–503`; `08c:307–392`) | Evaluate children before parents, keep one parameter, prove uniqueness by induction | A numerical algebra can be computable and total on its carrier without having a PA proof of that totality. Consequently its operations need not lift to an algebra in \(\mathcal B_{\mathrm{PA}}\). The syntactic initiality theorem cannot by itself establish the numerical universal property against all such algebras. | Retain the numerical universal-property proof. It already reuses §5's codes/parser rather than rebuilding them. |
| Generic image theorem vs all concrete derivation proofs (`a:473–510`; `05a:637–806`; `08c:424–473`; `04:401–423`; `09:469–527`) | Finite derivations eventually produce a least theory | The generic theorem starts with an **initial** derivation algebra. It constructs the least image; it does not prove an algebra of finite derivations is initial in any particular category. | Retain each concrete existence/initiality proof and the common image theorem. |
| §5 vs §7.4 derivations | Same tree codes, evaluation, and uniqueness | §5 needs \(\Sigma_1\) witness aggregation, T-provable totality, and T-provable graph equality. §7.4 needs the universal property against arbitrary numerical algebras and tuple-coded rule labels. Their ambient morphism requirements differ. | Retain. |
| §7.4 realization vs numerical/syntactic comparison (`08c:498–569`) | Induction on the same finite derivations | The comparison must translate labels through \(\eta_n^{-1}\rho_n\kappa_{m_n}^{-1}\), prove validity/conclusion preservation, and build an inverse. Initiality alone neither makes these carriers literally equal nor supplies this specified computable bijection. | Retain the label comparison and induction. |
| §7.4 vs Miller Proposition 8.5 (`04:372–423`) | Same computable finite-tree evaluation | The Miller proof must show membership outcome, evaluation domain, and evaluation result are the same for every representation \(p\in P_a\). A computation valid for one fixed oracle representation is insufficient for a morphism of \(\mathcal D_a\). | Retain the representation-independence argument and its termination/fiber checks. At most refer to the existing sequence/tree coding setup in one sentence; do not replace the proof by the ordinary numerical theorem. |
| Numerical syntax vs fork Proposition 9.2 (`09:360–403`) | Componentwise tree fold | Componentwise totality is insufficient: the component maps must satisfy \(z_i u_0=u_i\sigma_i\). Naturality of the algebra and induction establish that they form a morphism in \(\mathcal E\). | Retain. |
| Numerical derivations vs fork Proposition 9.3 (`09:469–527`) | Componentwise derivation evaluation | Valid axiom labels and conclusions must be preserved by relabeling, and the folds must obey \(Q(0\to i)u_0=u_i\rho_i\). A family of unrelated numerical initial algebras would not give the required functorial proof object. | Retain. |
| Numerical foundation vs §9 setup (`08c:18–276`; `09:41–48`) | Description of \(\mathcal C_{\mathrm{rec}}\) | §9 explicitly cites §7.4 and only recalls carriers and the notation used there; it does not reprove regularity, coproducts, or the numerical equivalences. | Already appropriately reused. |
| §9 nonempty words vs Appendix B (`09:96–125`; `b:274–341`) | Lists of tuples and entrywise relabeling | §9 introduces the particular \(V^\#\). Appendix B extends \((-)^\#\) to arbitrary objects and partial maps, with exact domains, proves a free-semigroup property, and gives the natural frame isomorphism. The shared first coordinate synchronizes word lengths in the frame map; numerical list initiality does not supply that map. | Retain. The four-line general definition in Appendix B is a harmless point-of-use restatement. |
| Empty-inclusive lists vs nonempty words (`08c:361–392`; `b:274–300`) | Finite sequence traversal | One is a parameterized initial algebra for \(1+V\times(-)\); the other is nonempty words with free-semigroup multiplication. The empty list and nil operation are absent from the latter. | Do not merge the universal properties. |

## Definition-order and dependency audit

The relevant notions are present and connected: Appendix A defines parameter stability before categorical syntax; defines syntax/list folds before free variables; defines option-valued substitution before its admissibility pullback; defines rule data and \(H\) before the least-image theorem; then specifies first-order/propositional rules. Section 5 introduces the source-predicate morphism condition and witness search before using evaluation records. The numerical realization refers back to those codes. Section 9 refers back to \(\mathcal C_{\mathrm{rec}}\), defines its functor category and component maps before constructing formula/proof relabelings. Appendix B's nonempty word construction is correctly separated from the empty-inclusive logical lists.

No revised outline is warranted by this duplication check. The minimum dependency-preserving intervention is the local replacement in §7.4 described above. The \(\mathcal B_{\mathrm{PA}}\) reference and the fork functor-law replacement are optional; neither justifies a broad compression of Appendix A or of the realization arguments.

## Scope

Read Appendix A in full, all of `05a-internal-syntax.tex` and `08c-numerical-realization.tex`, the realization and generated-theory proof in `04-miller-sequences.tex:304–498`, the setup and syntax/derivation realization portions of `09-three-point-space.tex:1–151,297–570`, and the finite-word/frame portion of Appendix B (`b:246–342`). The remaining portions of the Miller/cosheaf examples were not audited for repetition unrelated to these constructions. The attached Cockett text and supplied KLR text were consulted as described above. Page anchors come from the current auxiliary file; no fresh compilation or rendered-layout review was performed. This is an argument-duplication review, not a certification of all mathematical correctness or novelty.
