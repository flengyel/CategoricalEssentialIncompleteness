# Abstract assessment and division of material, version 37

**Manuscript:** Florian Lengyel, *Logical consequence and essential incompleteness in recursion categories*, version 37, 1 November 2026, commit `47be761bc05fa0d176b2f9a48f5f63db63b9fa79`.

The abstract should identify the contribution, state the principal results, and preserve their essential scope. It should not reproduce the introduction's account of the proof architecture. Version 37 overloads its summary with technical ambient-category and comparison machinery while listing the instances twice. Its reference to a generated theory can be made informative by briefly identifying it as the subobject of sentences derivable from the chosen axioms. The full connection from syntax through derivations, images, ranges, comparison, and theory extension belongs in the introduction.

The first recommendations in this audit demanded too much of the abstract. The reports recover a useful mathematical account, but recovering that account does not imply that every stage should appear in the abstract. This revised assessment distinguishes the two placements. It evaluates the reports rather than supplying a replacement abstract. The manuscript remains unchanged.

## 1. Current paper and abstract organization


The main outline was reconstructed from all fourteen section sources, including the nested arithmetic files; the appendix outline was reconstructed from all four appendices. Their combined account has the following mathematical progression:

1. **Computational obstruction (§3):** a source Turing morphism, a range-functor comparison, and the specified conditional lifts yield a criterion excluding completeness and a criterion for source inseparability.
2. **Internal logical consequence (Appendix A, applied in §4):** categorical syntax and inference rules, together with a chosen axiom subobject, determine finite derivations and a conclusion morphism. Its sentence-conclusion image is the generated sentence theory.
3. **Connection of deduction with categorical recursion (§4):** represent that theory by its restriction range; inverse image under sentence negation gives refutation. The comparison theorem and the separate source-inseparability extension criterion are applied to this pair.
4. **Realizations and applications (§§5–9):** first-order deduction in the syntactic and Miller settings, propositional deduction in the cosheaf setting, and the corresponding effective extension conclusions.
5. **Supporting results:** numerical realization and a second arithmetic proof; the cosheaf infrastructure; the lifting counterexample; and the auxiliary faithful all-model representation.

The manuscript's order is not itself the order an abstract must follow. The general deduction construction is in Appendix A, while §4 connects it to the earlier computational comparison. The introduction should explain that relationship. The abstract needs only enough conceptual identification to state what is constructed and then summarize the principal conclusions.

The present abstract has the pattern **general objective → specific realization list → general technical machinery → specific conclusions**. The result is a repeated instance inventory interrupted by details of the mechanism. General-to-specific order can instead govern a concise contribution-and-results summary; it need not become an introductory outline.

## 2. Mathematical Writing: source and application


The supplied KLR PDF and text were consulted directly. Printed pages are two less than the corresponding PDF pages in this copy. The following are paraphrases; the applications below are this review's judgments, not additional rules attributed to KLR.

| Verified source | Relevant advice |
| --- | --- |
| Knuth, §1, points 10–13, pp. 2–3 | Connect the exposition, explain definitions, motivate what follows, and preserve meaning when formulas are skimmed. |
| Knuth, §1, point 17, p. 3; points 24 and 26, p. 5 | Make sentences readable, give the opening particular care, and avoid unnecessary jargon and noun strings. |
| Knuth, §§4–5, pp. 9–13 | Definition placement is contextual; postponement can work, but too much withheld meaning obstructs reading. |
| Herbert Wilf, §27, p. 59 | Give readers an early, plain account of the work and make its results identifiable. |
| Leslie Lamport, §31, pp. 69–71 | Establish the idea and audience; improve the organization rather than repairing isolated sentences alone. |
| Paul Halmos, §42, pp. 106, 111–112 | Organize without distracting; alternative mathematical threads need connections, not merely linear placement. |

These passages discuss mathematical exposition and papers; they do not prescribe the contents of a research abstract. No dedicated research-abstract recipe, prescribed sentence count, or universal word limit was located in these discussions. They do not justify requiring the complete construction or proof progression inside the abstract. The content priorities below are editorial judgments for this paper, not a formula quoted from KLR. The source is Knuth, Larrabee, and Roberts, *Mathematical Writing*, available at https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf.

## 3. Concrete abstract findings

The anchors refer to abstract.tex in version 37, manuscript p. 1. The distinction between an abstract and an introduction governs these recommendations.

| Anchor | Difficulty | Action and location |
| --- | --- | --- |
| Sentence 4, lines 9–10: “These constructions take place in the regular categories of total morphisms in the restriction splittings.” | An unexplained classification of the setting interrupts the summary. Its referent can be inferred, but the statement supplies no result that the reader needs at this point. | Delete the standalone sentence from the abstract. Retain the completion qualification in the contribution statement. Explain what is split and why in the introduction when needed; state the exact category and hypotheses in the body. |
| Sentence 5, lines 11–12: “generated theories.” | The term does not identify the input or logical output: the theories are generated from chosen axioms by the internal deductive system. | If the term is retained, give the brief identification “subobjects of sentences derivable from chosen axioms.” The full derivation/conclusion-image construction belongs in the introduction. |
| Sentences 6–9, lines 13–18 | Range functors, validity subobjects, inverse images, reductions, and conditional lifts form a technical checklist. It is too detailed for the summary while still insufficient as an introductory account. | Summarize the categorical incompleteness result at an appropriate level, preserving its conditional scope. Explain the connections and the distinction between the two arguments in the introduction; retain all exact hypotheses in the theorems. |
| Sentences 2–3 and 10–14 | The categories and logics are listed before the technical material, then listed again with conclusions. | Give the general contribution first, then state each principal instance together with its result, once. |
| Uniform independence and arithmetic-ultrapower soundness | These are substantial results, but naming all substantial results is not the abstract's job. | Include an additional result only when it improves the summary. The introduction can explain both; their presence in the paper does not force their inclusion in the abstract. |

The full source outline is in the companion paper_outline_v37.md. The principal application scopes must remain explicit: all consistent c.e. PA extensions; the Miller single-program semidecision condition over every binary representation; and consistent same-language c.e. extensions of the two propositional endpoint theories. Shortening must not turn one of these into an unrestricted extension claim.

## 4. Account for the introduction: what the theories are

For a recursion category \(\mathscr R\), put
\[
 \mathscr S=\operatorname{Split}(\mathscr R),\qquad
 \mathcal D=\operatorname{Tot}(\mathscr S).
\]
The general construction assumes the regularity, syntax, and initial algebras needed in \(\mathcal D\); the applications prove these properties for their particular categories.

Let \(\Phi\in\mathcal D\) be the formula object, let \(j:S\hookrightarrow\Phi\) be its sentence subobject, and choose an axiom subobject \(i_A:A\hookrightarrow S\). The syntax, inference rules, and chosen axioms define an inference endofunctor
\[
 H_A:\mathcal D/\Phi\longrightarrow\mathcal D/\Phi.
\]
Its initial algebra has underlying conclusion morphism \(c_A:P_A\to\Phi\). Restricting to sentence conclusions gives \(c_{A,S}:P_{A,S}\to S\), whose regular image is
\[
 P_{A,S}\twoheadrightarrow T_{A,S}\xhookrightarrow{m_A}S.
\]
The generated sentence theory \(T_{A,S}\hookrightarrow S\) is the least deductively closed sentence subobject containing \(A\). It is the deductive closure of those axioms in that internal system (Theorem A.6 and the following paragraph; Theorem 5.9).

When \(m_A\) has the specified partial inverse in \(\mathscr S\), the same theory is represented by the restriction idempotent
\[
 t_A=\operatorname{ran}(c_{A,S}):S\rightharpoonup S.
\]
For the total sentence-negation morphism \(\nu:S\to S\), its inverse image \(\nu^*t_A\) represents refutability. These are the theorem and refutation domains used in the incompleteness criteria. The image-to-range identification connects the logical construction with the categorical recursion argument.

The introduction should explain this connection and distinguish the two arguments: semantic comparison in Theorem 4.2, and persistence of a fixed inseparable-pair reduction in Corollary 4.3. The exact hypotheses and full typed construction remain in the body. The abstract can identify the output simply as the theories of sentences derivable from chosen axioms in the internal deductive systems.

## 5. What belongs in the abstract and introduction


The two documents have different jobs.

**Abstract:** summarize the contribution and principal results with their essential scope. A suitable content outline is:

1. **General contribution and objective:** internal propositional and first-order deductive systems in the realized recursion-category completions, used to obtain essential-incompleteness results addressing Di Paola and Heller's objective.
2. **Minimal identification of the logical output:** if generated theories are named, identify them briefly as subobjects of sentences derivable from chosen axioms. This is an identification of the contribution, not an account of the proof architecture.
3. **Instances and principal conclusions in one pass:** the syntactic/arithmetic first-order realization, the Miller first-order realization, and the cosheaf propositional realization, each connected directly to its conclusion. Preserve the arithmetic c.e. extension scope, Miller's single-program/every-representation condition, and the propositional same-language c.e. condition.
4. **Selective additional results:** uniform independent-sentence selection or ultrapower soundness can be included only if they are important enough to the summary and do not crowd out the contribution and principal conclusions. There is no requirement to inventory all strengthened results.

A short reference to the categorical comparison method may fit this summary. A full explanation of domains, reductions, lifting, and persistence is not required. Nor does every familiar technical term need a definition in the abstract.

**Introduction:** explain the mathematical relationship that the reports reconstructed:

- categorical syntax and internal rules, with a chosen axiom subobject;
- finite derivations and their sentence-conclusion morphism;
- its image as the generated sentence theory, represented by a restriction range;
- negation's refutation domain;
- the computational role of the Turing morphism and the semantic-comparison or source-inseparability criteria;
- consistency, theory extension, and why the permitted extension classes yield essential incompleteness;
- the different functions of the three principal applications and the auxiliary realizations.

The full typed construction and exact hypotheses remain in the body. The introduction supplies the connecting explanation. The abstract states what was accomplished. Our earlier proposed abstract outline improperly promoted this introductory sequence into a set of abstract requirements.

## 6. Evaluation of the agent recommendations

The two outlines and the independent construction account recover the same mathematical relationship. The theory is the system's deductive closure of chosen axioms, and its restriction-domain representation is used in the incompleteness argument. That account is useful for the introduction and for checking every short description of the contribution.

The earlier recommendation to require that entire chain in the abstract is withdrawn. In particular, the abstract is not required to explain the Turing morphism's role, the conditional-lifting construction, or persistence of a reduction under theory extension. The introduction should make those connections. The abstract states the construction and principal conclusions, with enough identification and qualification to make those claims intelligible.

The writing assessment retains two specific criticisms: the isolated total-morphism/restriction-splitting classification and the duplicated instance inventory. It also retains the need to identify what “generated theory” denotes if that phrase appears. KLR's advice about connected exposition supports these judgments, but does not supply a rule requiring an introductory outline in an abstract.

## Scope and preservation

Five agents supplied a full main-section outline, a full appendix outline, an independent deduction-to-theory account, a source-based Mathematical Writing assessment, and an evaluation of the reports. The outliners read all fourteen main-section sources and all four appendices completely. The construction and writing agents checked the central argument chains and the relevant application statements. The reducer checked the reports, the key source statements, and the cited KLR passages. Result numbers and section starting pages were checked against the compiled labels.

This is an organization and explanation assessment. It does not certify every proof, bibliography entry, or originality claim. The recorded hashes confirm that all 22 manuscript source files remain unchanged. The paper remains version 37; no new abstract or introduction was installed.
