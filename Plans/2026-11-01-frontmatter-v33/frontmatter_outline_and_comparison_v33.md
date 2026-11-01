# Abstract, introduction, and related work: outline and comparison

**Paper:** Florian Lengyel, *Logical consequence and essential incompleteness in recursion categories*, version 33, 1 November 2026, commit `0531db597e015824af5861a8e5ad0c1976efdcb3`.

The opening should explain the Di Paola–Heller program and the paper's construction of logical consequence before introducing the comparison theorem's technical hypotheses. The present abstract reports applications but omits the construction named by the title. The introduction gives the internal deductive structure a subsidiary role and describes an all-model interpretation that is now auxiliary to the main arithmetic proof. These are problems of organization and explanation; rearranging the existing theorem summaries alone would not supply the missing connection.

This report supplies an outline and source comparisons before a rewrite. The manuscript remains version 33. A companion **Detailed outline of version 33** lists every existing section and subsection with its mathematical role and principal results.

## 1. Existing front matter

| Passage | What it currently does | What the revised exposition needs |
| --- | --- | --- |
| Abstract, sentences 1–2 | Announces inseparability and range-functor comparison. | Identify the internal syntax, derivations, and generated theories to which the comparison applies. |
| Abstract, remaining sentences | Summarizes arithmetic, Miller, a functor counterexample, and cosheaves. | Preserve the different extension classes; preview the strengthened arithmetic and soundness results without crowding out the construction. |
| Introduction, paragraphs 1–2 | Starts with Corollary 3.3, conditional lifts, and a counterexample. | State the problem and the logical meaning of the objects before the hypotheses. Relocate the useful conditional and counterexample material. |
| Paragraphs 3–4 | Develops Miller's category, cut sets, and field theory. | Explain the common method first, then give this application enough room to distinguish representation independence from computation with one fixed representation. |
| Paragraph 5 | Combines the definition of S_T, nonlocal connectedness, all-model interpretation, and internal syntax. | Separate syntactic realization from soundness. The fixed-category arithmetic proof uses standard codes and a separate model of the represented axioms. |
| Paragraph 6 | Joins arithmetic and cosheaf applications in one paragraph. | Give the two applications separate purposes and explain their extension statements. |
| Paragraph 7 | Provides a roadmap. | Retain a short dependency-based roadmap after the mathematical overview. |
| Related work, four paragraphs | Introduces the DPH motivation late, lists categorical frameworks and inseparability results, then returns to Miller. | Move the motivation to the opening. Replace the catalogue with source-specific comparisons. Remove repeated descriptions of the present Miller result. |

The current front matter also omits the uniform independent-sentence theorem and the soundness transport to arithmetic ultrapowers. Its section references are current, and the qualifications about lifting and uniform semidecidability are substantive. They should be relocated or explained, rather than deleted.

## 2. Knuth–Larrabee–Roberts: verified guidance

KLR paraphrases follow; body PDF pages are printed pages plus two.

| Source | Guidance relevant here |
| --- | --- |
| Knuth, §1, points 10–13, pp. 2–3 | Connect explanations, introduce variables, motivate results, and make prose readable without formulas. |
| Knuth, §1, points 24 and 26, p. 5 | Give the opening special care and avoid unnecessary jargon. |
| §§4–5, pp. 9–13 | Place definitions in context, near their uses. |
| Herbert Wilf, §27, pp. 59–60 | Introduce the subject promptly; make results identifiable. |
| Leslie Lamport, §§31–32, pp. 69–71 | Organize conceptually, begin directly, and remove ceremonial exposition. |
| Knuth, §15, pp. 32–33 | Relevant prior work can improve a paper's technical quality. |
| Paul Halmos, §42, pp. 106, 111–112 | Weave mathematical threads together instead of listing results. |

Van Leunen's §36 précis exercise (p. 87) is not a research-abstract template or sentence limit.

## 3. Mathematical account the opening must explain

The paper has two related routes to incompleteness. The introduction should explain their connection while distinguishing their hypotheses.

**Construction of consequence.** In a regular category \(\mathcal D\) with the required initial algebras, an initial inference algebra in \(\mathcal D/\Phi\) has conclusion morphism \(c_A:P_A\to\Phi\). Its regular image is the least deductively closed formula subobject containing the axioms. Pullback to the sentence object \(S\hookrightarrow\Phi\) gives the generated sentence theory. Under the stated partial-inverse hypotheses, its image is represented by the restriction range \(t_A=\operatorname{ran}(c_{A,S})\). Negation gives the refutation domain by inverse image. These are the constructions of Appendix A and their realizations.

**Semantic comparison.** Proposition 4.1 uses a soundness factorization and a validity subobject disjoint from its negated inverse image to obtain disjoint interpreted theorem and refutation domains. Theorem 3.1, applied in Theorem 4.2, uses the specified lifted partial conditional and reduction inequalities to produce a total morphism avoiding both interpreted domains. This yields incompleteness under the theorem's categorical hypotheses.

**Consistent extensions.** Corollary 4.3 uses a fixed inseparable source pair and a total reduction to the theorem and refutation domains. The reduction persists when the theory grows; consistency prevents the larger domains from meeting. The abstract statement concerns represented consistent extensions. The concrete realizations supply their effective presentation classes. Essential incompleteness requires this extension argument or application-specific verification throughout the stated extension class. Arithmetic also verifies the lifted-separator argument for every permitted consistent extension.

For arithmetic, the distinction between two semantic roles is essential. The standard model N interprets codes and operations in the fixed category S_PA. A separately chosen structure K models the represented axiom set Γ. Consistency of Γ supplies such a K; the proof does not require N to satisfy Γ. Section 6 transports the standard-code soundness factorization to arithmetic ultrapowers through a natural comparison. The faithful family of all models in Appendix D is an auxiliary representation result.

## 4. Proposed abstract outline

Use one connected paragraph with the following sentence functions. These are content priorities, not a prescribed sentence count.

1. **Subject and contribution:** construct logical consequence in suitable completions of recursion categories and obtain criteria yielding essential incompleteness.
2. **Logical construction:** initial algebras specify syntax and finite derivations; regular images of conclusion morphisms give generated deductive theories.
3. **Comparison mechanism:** state the role of sound semantic interpretation, the required conditional lifts, and the inseparability argument that survives consistent extension.
4. **Arithmetic:** state the conclusion for consistent c.e. extensions of PA, with a concise indication of standard-code/ultrapower soundness and uniform independent sentences.
5. **Miller:** state the real-closed-field application with its uniform-in-all-representations semidecidability condition.
6. **Cosheaves:** state essential incompleteness of the two propositional endpoint theories arising from the three-point construction.

The fixed-representation separator counterexample can be explained in the introduction if it makes the abstract too dense. The abstract should not become a bibliography or a list of theorem numbers. The Di Paola–Heller motivation must be explicit in the introduction; naming the program in the abstract is optional.

## 5. Proposed introduction outline

Each item has one mathematical purpose. The existing body order need not change.

| Paragraph | Purpose and required content | Main anchors |
| --- | --- | --- |
| I1. Program and question | Open with Di Paola–Heller's categorical formulation of **generalized incompleteness**. Explain the question connecting partial computation with provable/refutable sentences, then state the part addressed by this paper. | DPH §1, pp. 594–596; §§3–4 of this paper. |
| I2. Internal logical consequence | Explain formula and sentence objects, initial derivations, the conclusion morphism, and its regular image as generated deductive closure. Name the suitable total completion and its hypotheses. | Appendix A.5–A.7; Theorem 5.9. |
| I3. Logical comparison | Explain what a range functor interprets and why semantic consistency, reductions, and a lifted reversed conditional produce undecidable sentences. Introduce the theorem by its purpose before its technical data. | Theorem 3.1; Proposition 4.1; Theorem 4.2. |
| I4. Inseparability and extension | Explain the second route through a fixed inseparable pair, persistence under consistent extension, and why lifting is substantive. Retain the sufficient condition using disjoint joins and the counterexample. | Corollaries 3.3, 4.3; Proposition 3.4; Appendix C. |
| I5. Syntactic realization | Introduce S_T by universally T-provable graph equality. Explain that Tot(Split(S_T)) realizes syntax, substitution, derivations, and generated theories. The arithmetic application fixes S_PA while its represented axioms vary. | §5, especially Lemma 5.3 and Theorem 5.9. |
| I6. Soundness and ultrapowers | Distinguish code interpretation in N from truth in K⊨Γ. Explain the soundness factorization and its transport to arithmetic ultrapowers. | Proposition 6.6; Theorem 6.9. |
| I7. Arithmetic and uniformity | State theorem/refutation inseparability for every consistent c.e. PA extension. Mention the indexed theory family and one morphism q:E→S selecting an independent sentence on every consistent standard fiber. | Corollary 7.4; Proposition 7.5; Theorem 7.6 in §7.3. |
| I8. Miller computation | Explain representation-independent partial computation and the inseparable cut pair. Contrast this with separation after fixing one representation. | §8.1–8.2. |
| I9. Miller theory | Describe the field theory and its exact uniform semidecidability extension class. Explain the reduction from the cut pair to theorem/refutation domains. | Theorem 8.6. |
| I10. Cosheaf theories | Explain the three-point recursion category, its completion, generated propositional theories, and the two endpoint conclusions. State the same-language c.e. extension class. | §9; Corollary 9.6; Appendix B. |
| I11. Roadmap | Direct the reader through the comparison, logical construction, realizations, soundness, and applications. Identify the auxiliary role of the faithful all-model family. | Current section order; Appendices A–D. |

Keep the syntax and soundness explanations separate. Keep the Miller construction and its logical application separate if combining them would conceal the effectiveness condition. Related work can precede the final roadmap; that placement is an editorial choice, not a KLR rule.

## 6. Related-work outline and verified comparisons

The literature should be organized by mathematical relationships. The following order gives each comparison a function.

### Historical semantic and provability categories

Montagna's concluding remark, pp. 114–115, proposes connecting a recursion category reflecting true arithmetic with a syntactic p-recursion category reflecting formal arithmetic. DPM pp. 643–646 study the uniformly provable and proposed pointwise quotients as guides to the program and to broader existence theorems. Neither inspected passage specifies a functor S_T→S'_T. Use the semantic/formal motivation without attributing that additional construction.

Distinguish a single proof T⊢∀x E(x) from separate proofs T⊢E(n) at each standard n. Lengyel, arXiv v2, Corollary 2, p. 5, proves that the latter equality does not respect the proposed composition for consistent c.e. T⊇PA. Thus the proposed S'_T, including S', does not define a category under that composition. The valid S_T and S constructions are unaffected. This explains why the present construction uses universal graph equality and actual semantic interpretation functors.

### Earlier categorical inseparability

DPH §1 explicitly includes incompleteness of consistent effective extensions among its generalized-incompleteness formulations. Their Theorem 8.15, pp. 625–626, constructs inseparable domains under their dominical choice/coproduct hypotheses. Compare the precise assumptions with the present range-functor/lifting criterion and the further construction of internally generated deductive theories.

Bernardi §2 and §3, especially Theorem 2, p. 128, develops fixed-point and inseparability results from precomplete equivalence relations, including PA-provable equality of program indices as an example. Preserve this substantive antecedent. The present comparison additionally concerns initial derivations, generated theory images, semantic soundness, and the specified extension classes. The mere existence of inseparable domains is not the distinguishing contribution: Montagna also records effective inseparability in S in Remark 3.1, p. 114.

### Partial-map representation and Turing structure

Rosolini's thesis and Theorem 1.2 of the 1988 chapter represent p-categories using suitable partial-map categories; the chapter's theorem gives a full p-subcategory embedding. Domain splitting is directly relevant to the present total restriction splitting. Robinson–Rosolini pp. 108–109 supplies a PA-functional-Σ₁ antecedent, attributed there to Montagna. The current paper proves its own many-object predicate presentation, regularity, and partial inverses.

Cockett–Hofstra (2008) supplies Turing-category structure, its relation to partial combinatory algebras, and the halting-domain completeness result in Corollary 3.9. Keep those results with structural background. Heller's existence theorem and the subsequent iteration-functor results concern construction of recursion categories; the present comparison starts with an existing Turing morphism. Local connectedness retains its mathematical and historical roles without becoming a premise of the current central comparison.

### Diagonal and categorical incompleteness antecedents

Lawvere's 1969 paper already contains a logical incompleteness theorem in §3, pp. 144–145, using definable substitution and representable provability. His §2 also gives a finite-product/evaluation formulation of the diagonal mechanism. Yanofsky's §5 develops the diagonalization lemma and explicit Gödel–Rosser applications. Essential incompleteness cannot therefore be presented as something fixed-point approaches inherently cannot yield.

Cockett's sole-author *Categories and Computability* (2014), §7.5, Theorem 7.14, is a separate direct antecedent: under its Turing-category, nontriviality, restriction-zero/join and provability-predicate assumptions, it obtains a predicate of the terminal object different from zero and identity. Its assumed predicate concerns extensional program order. Compare that datum with the present construction of derivations and generated theorem ranges. Do not attribute this theorem to the joint 2008 paper.

### Ramesh and internal arithmetic presentation

Sridhar Ramesh's *Introspective Theories and Geminal Categories* (2023), Definitions 2.1–2.2, concerns a finite-limit category, an internal finite-limit category, and an indexed finite-limit-preserving functor from the self-indexing to the represented indexed category. The arithmetic Construction 2.9, pp. 49–52, starts from Σ₁ predicates and provable functional graphs, then uses an ex/reg completion. This is a concrete comparison with our predicate presentation.

Ramesh's introspective data yield Löb/guarded fixed-point results (Theorem 4.19, p. 82). The present established output is internal syntax and deductive closure together with interpretation and incompleteness comparisons. Identifying our completion as an introspective theory, or iterating it to obtain the required indexed/internal-category and quotation data, would require additional constructions and coherence proofs. No such result is claimed in the current paper. In the introduction, state the different constructions positively; the unproved identification is an editorial boundary, not a proposed defensive paragraph.

### Syntax, Miller, and cosheaf antecedents

Keep the detailed initial-algebra and binding/substitution precedents with the constructions in Appendix A. A short pointer in Related work may explain the use of established syntax machinery; it should not repeat every appendix citation.

For Miller and Bauer–Hanson, retain the exact stronger index property and binary-representation convention used in §8. Their role is to supply the sequence and representation setting. Compare their applications with our recursion category, inseparable cut pair, fixed-representation separating functors, and field-theory extension result. The cosheaf background can remain beside the three-point construction in §9; it need not be added to Related work merely for symmetry.

## 7. Use of LOCOct10f and remaining source limit

The local LOCOct10f source matches the note in `flengyel/notes`, Git blob `781fbfae0935faff58a87435ef85cbc5d9540aea`. Its introduction and inseparability comparison identify useful historical relationships. Its earlier local-connectedness theorem hierarchy should not be substituted for the present proof.

Two Rosolini claims in that note require separate treatment: the foundational representation comparison is verified; the quotation and criticism concerning p. 313 of the 1988 chapter were not independently verified because the original page was inaccessible. They are excluded from the proposed positive account. The absence of verification is not a finding that the claim is false. It does not prevent the verified representation comparison from being included.

## References and source versions

- **KLR:** D. E. Knuth, T. Larrabee, and P. M. Roberts, *Mathematical Writing*, Stanford report CS-TR-88-1193, 1988, based on the 1987 course. [Stanford text](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf).
- **DPH:** R. A. Di Paola and A. Heller, *Dominical categories: recursion theory without elements*, J. Symbolic Logic **52** (1987), 594–635. [DOI](https://doi.org/10.2307/2274352).
- **Montagna:** F. Montagna, *“Pathologies” in two syntactic categories of partial maps*, Notre Dame J. Formal Logic **30** (1989), 105–116. [DOI](https://doi.org/10.1305/ndjfl/1093634998).
- **DPM:** R. A. Di Paola and F. Montagna, *Some properties of the syntactic p-recursion categories generated by consistent, recursively enumerable extensions of Peano arithmetic*, J. Symbolic Logic **56** (1991), 643–660. [DOI](https://doi.org/10.2307/2274707).
- **Composition:** F. Lengyel, *Pointwise provable equality and the failure of composition*, [arXiv:2609.25556v2](https://arxiv.org/abs/2609.25556v2), 2026. The theorem locators above refer to arXiv v2, not the separately maintained author version 37.
- **Bernardi:** C. Bernardi, *Precomplete equivalence relations in dominical categories*, Proc. Amer. Math. Soc. **98** (1986), 124–134. [DOI](https://doi.org/10.1090/S0002-9939-1986-0848889-9).
- **Rosolini thesis:** G. Rosolini, *Continuity and effectiveness in topoi*, Oxford D.Phil. thesis, 1986. The inspected author-uploaded text is the 1995 recovered/retypeset edition, which warns of possible discrepancies from the original. [Author's copy](https://www.researchgate.net/profile/Giuseppe-Rosolini/publication/35103849_Continuity_and_effectiveness_in_topoi/links/57ef75b908ae886b89741067/Continuity-and-effectiveness-in-topoi.pdf).
- **Rosolini chapter:** G. Rosolini, *Representation theorems for P-categories*, in F. Borceux (ed.), *Categorical Algebra and its Applications*, LNM **1348**, Springer, 1988, 307–315. [DOI](https://doi.org/10.1007/BFb0081368).
- **Robinson–Rosolini:** E. Robinson and G. Rosolini, *Categories of partial maps*, Information and Computation **79** (1988), 95–130. [DOI](https://doi.org/10.1016/0890-5401(88)90034-X).
- **Cockett–Hofstra:** J. R. B. Cockett and P. J. W. Hofstra, *Introduction to Turing categories*, Ann. Pure Appl. Logic **156** (2008), 183–209. [DOI](https://doi.org/10.1016/j.apal.2008.04.005).
- **Cockett:** J. R. B. Cockett, *Categories and Computability*, author-hosted notes, 12 August 2014. [Text](https://cspages.ucalgary.ca/~robin/talks/estonia-winter-2010/estonia-notes.pdf).
- **Lawvere:** F. W. Lawvere, *Diagonal arguments and cartesian closed categories*, *Category Theory, Homology Theory and their Applications II*, LNM **92**, Springer, 1969, 134–145. [DOI](https://doi.org/10.1007/BFb0080769). Locators use original pagination; [original scan](https://www.its.caltech.edu/~matilde/LawvereDiagonalArgCartesianClosedCats.pdf).
- **Yanofsky:** N. S. Yanofsky, *A Universal Approach to Self-Referential Paradoxes, Incompleteness and Fixed Points*, Bull. Symbolic Logic **9** (2003), 362–386. [DOI](https://doi.org/10.2178/bsl/1058448677); [author preprint](https://arxiv.org/abs/math/0305282). Section/page locators above use the preprint.
- **Ramesh:** S. Ramesh, *Introspective Theories and Geminal Categories*, Ph.D. dissertation, University of California, Berkeley, 2023. [Institutional record and text](https://escholarship.org/uc/item/3mn0c475).
- **Miller:** J. S. Miller, *Degrees of unsolvability of continuous functions*, J. Symbolic Logic **69** (2004), 555–584. [DOI](https://doi.org/10.2178/jsl/1082418543).
- **Bauer–Hanson:** A. Bauer and J. E. Hanson, *The Countable Reals*, [arXiv:2404.01256v3](https://arxiv.org/abs/2404.01256v3), 2026.

The mathematical-writing reviewer read the complete current front matter and the relevant KLR discussions; the outliner read all 22 compiled TeX files; three literature reviews checked the sources above; and a separate agent reconciled their conclusions. The original journal scans controlled the DPH/Montagna/DPM checks. Bernardi was checked through the complete author-uploaded primary text. The unresolved Rosolini page is recorded above. No proof, bibliography entry, or manuscript section has been changed in preparing this outline.
