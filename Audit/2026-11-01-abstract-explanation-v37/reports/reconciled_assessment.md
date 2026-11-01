# Reconciled assessment of the version 37 abstract

**Manuscript:** Florian Lengyel, *Logical consequence and essential incompleteness in recursion categories*, version 37, 1 November 2026, commit `47be761bc05fa0d176b2f9a48f5f63db63b9fa79`.

The abstract should identify the contribution, state the principal results, and preserve their essential scope. It should not reproduce the introduction's account of the proof architecture. Version 37 overloads its summary with technical ambient-category and comparison machinery while listing the instances twice. Its reference to a generated theory can be made informative by briefly identifying it as the subobject of sentences derivable from the chosen axioms. The full connection from syntax through derivations, images, ranges, comparison, and theory extension belongs in the introduction.

The first recommendations in this audit demanded too much of the abstract. The reports recover a useful mathematical account, but recovering that account does not imply that every stage should appear in the abstract. This revised assessment distinguishes the two placements. It evaluates the reports rather than supplying a replacement abstract. The manuscript remains unchanged.

## 1. What the actual outline establishes

The main outline was reconstructed from all fourteen section sources, including the nested arithmetic files; the appendix outline was reconstructed from all four appendices. Their combined account has the following mathematical progression:

1. **Computational obstruction (§3):** a source Turing morphism, a range-functor comparison, and the specified conditional lifts yield a criterion excluding completeness and a criterion for source inseparability.
2. **Internal logical consequence (Appendix A, applied in §4):** categorical syntax and inference rules, together with a chosen axiom subobject, determine finite derivations and a conclusion morphism. Its sentence-conclusion image is the generated sentence theory.
3. **Connection of deduction with categorical recursion (§4):** represent that theory by its restriction range; inverse image under sentence negation gives refutation. The comparison theorem and the separate source-inseparability extension criterion are applied to this pair.
4. **Realizations and applications (§§5–9):** first-order deduction in the syntactic and Miller settings, propositional deduction in the cosheaf setting, and the corresponding effective extension conclusions.
5. **Supporting results:** numerical realization and a second arithmetic proof; the cosheaf infrastructure; the lifting counterexample; and the auxiliary faithful all-model representation.

The manuscript's order is not itself the order an abstract must follow. The general deduction construction is in Appendix A, while §4 connects it to the earlier computational comparison. The introduction should explain that relationship. The abstract needs only enough conceptual identification to state what is constructed and then summarize the principal conclusions.

The present abstract has the pattern **general objective → specific realization list → general technical machinery → specific conclusions**. The result is a repeated instance inventory interrupted by details of the mechanism. General-to-specific order can instead govern a concise contribution-and-results summary; it need not become an introductory outline.

## 2. Mathematical account for the introduction and reference

Let `R` be the recursion category, `S_R=Split(R)` its restriction splitting, and `D=Tot(S_R)` the category in which the logical data and total conclusion morphisms are constructed. The general argument assumes the requisite regularity and initial algebras; the application sections establish those properties in the actual realizations.

The following typed account is useful for the introduction and for checking terminology; it is not a list of material required in the abstract. For a formula object `Φ∈D`, sentence subobject `j:S↪Φ`, and axiom subobject `A↪S`, the initial inference algebra has underlying conclusion morphism `c_A:P_A→Φ`. Restricting to sentence conclusions gives

\[
 c_{A,S}:P_{A,S}\longrightarrow S.
\]

Its regular image `T_{A,S}↪S` is the least sentence theory containing `A` (Theorem A.6 and the following paragraph). It represents the sentences derivable from those axioms by the internal rules. This answers the questions of where the theories live and how they belong to the internal deductive systems. In the abstract, the brief identification “the subobject of sentences derivable from the chosen axioms” can convey the output without the full account.

When the image inclusion has the stated partial inverse, the same subobject is represented by

\[
 t_A=\operatorname{ran}(c_{A,S}):S\rightharpoonup S
 \quad\text{in }S_R.
\]

For total sentence negation `ν:S→S` in `D`, the restriction domain `ν* t_A` represents refutable sentences. The construction therefore supplies the logical theorem/refutation pair on which the categorical comparison operates. It does not construct a further independent theory outside the internal system, nor a single object classifying all theories.

The formula and sentence stages should not be collapsed carelessly. The image of `c_A:P_A→Φ` is the generated formula subobject; the generated **sentence** theory is obtained by restricting conclusions to `S`. An abstract can describe this without the symbols by referring to finite derivations with sentence conclusions.

## 3. Evaluation of the recommendations

| Recommendation | Decision and reason |
| --- | --- |
| Remove the standalone sentence about regular categories of total morphisms and restriction splittings. | **Accept.** Its technical meaning is established in §§2 and 4 and in the realization statements, but the abstract gives neither its role nor its base category explicitly. Adding “of the recursion categories” repairs only one referent. Retaining the opening's completion qualification preserves the location of the constructions without interrupting the explanation. |
| Identify what a generated theory is. | **Retain a minimal identification in the abstract.** It is the subobject of sentences derivable from the chosen axioms. The detailed chain through finite derivations, conclusion images, range representation, and negation belongs in the introduction. If the abstract's contribution statement can name the construction clearly without the term “generated theory,” it need not add a definition merely to retain that phrase. |
| Retain initial algebras and regular images as the method. | **Optional in the abstract; explain in the introduction.** These are central mathematical ingredients and can be named briefly if they help state the contribution. They should not force the abstract to reproduce their input/output construction. Their full logical role belongs in the introductory explanation. |
| Require an account of the Turing morphism's role in the abstract. | **Reject that requirement.** This is valuable introductory material, but an abstract need not explain how the computational obstruction is produced. If it mentions the Turing argument, preserve the fact that the comparison or conditional hypotheses are substantive; a Turing morphism alone is not asserted to give an inseparable theorem/refutation pair. |
| Remove the validity-subobject checklist from the abstract. | **Accept.** The introduction should explain its semantic role; the theorem states the exact factorization and disjointness conditions. An abstract can summarize the soundness/comparison result at an appropriate level, or omit that intermediate result in favor of the principal conclusions. It must not turn bare soundness into an unconditional incompleteness theorem. |
| Explain persistence under consistent axiom extension in the abstract. | **State the extension conclusion, but do not require the proof explanation.** The abstract must preserve the permitted extension classes because they define the essential-incompleteness result. The account of growing theorem domains, persistent total reductions, and the two distinct proof routes belongs in the introduction. |
| Combine semantic comparison and source inseparability into one automatic consequence of a range functor. | **Reject.** Theorem 4.2 and Corollary 4.3 have different hypotheses. Neither range preservation nor soundness alone proves essential incompleteness. The abstract may summarize their shared purpose, but must not erase the distinction in what is established. |
| Require both uniform independent-sentence selection and ultrapower transport in the abstract. | **Reject as a requirement.** Neither is needed to explain the basic deduction-to-theory connection. Uniform selection is a directly related strengthening and can remain if space permits. Arithmetic-ultrapower soundness is substantial but is not needed to obtain the essential-incompleteness conclusion using the standard interpretation; its full account belongs in the introduction. The earlier priority of mentioning every strengthened result should yield to the central explanation. |
| State the three examples once, each with its logical realization and conclusion. | **Accept.** This keeps the general-to-specific order. The precise Miller extension class and the same-language c.e. condition for the propositional endpoints must survive any shortening. |

The phrase “three principal applications” is more exact than treating the body as having exactly three categorical realizations: §7.4 also gives the ordinary numerical realization, used as a foundation and a second arithmetic argument. No fourth application needs to be added to the abstract merely to enumerate all constructions.

## 4. Recommended placement and abstract outline

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

## 5. Mathematical Writing judgment and scope

The KLR assessment is supported by the actual source: Knuth §1, pp. 2–3 and 5 concerns connected, reader-oriented explanation; Lamport §31, pp. 69–71 addresses organization of the idea rather than merely local sentence repair; Halmos §42, pp. 111–112 addresses weaving mathematical threads together. The book supplies guidance for judging communication. It supplies no research-abstract template that forces every theorem or every categorical ambient construction into the abstract.

The resulting judgment is that version 37's abstract is overloaded with technical mechanism and repeated instance listing. It needs a more selective contribution-and-results summary, with a minimal identification of generated theories if that phrase is retained. The whole-paper outlines are useful for selecting that summary and for writing the introduction. They do not justify requiring the abstract itself to teach the complete connection from axioms to essential incompleteness. The recommended action is to remove the isolated ambient-category classification, avoid the double inventory, and reserve the fuller account for the introduction.

Read for this synthesis: all four specialist reports, the complete current abstract, §4's theory construction and extension criterion, Appendix A's image theorem and first-order theory construction, the Miller theory-extension proof, the uniform independent-sentence theorem, the ultrapower-soundness statement, and the cited KLR passages. The main and appendix outline agents read all compiled substantive sources. This is an explanation and dependency assessment, not a new correctness, bibliography, or originality audit. No manuscript file was edited and no full replacement abstract was written.
