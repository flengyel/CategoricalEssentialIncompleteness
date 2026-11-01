# Outline and organization review of manuscript v20

**Manuscript:** *Logical consequence and essential incompleteness in recursion categories*, version 20, 1 November 2026, 61 pages; repository commit `c182b1b2c54af499e0ef6f3f7ae6f179eaa55b65`.

**Conclusion.** The comparison theorem has an appropriate place: Theorem 3.1, p. 5, in its own subsection §3.1 within the dedicated §3, “Diagonal comparison and lifted partial conditionals” (pp. 4–7). That section also proves the local-connectedness criterion and the source-inseparability consequence. Splitting it into additional sections is unnecessary. The main unfinished organizational task is to connect the new internal-theory result, Theorem 4.2, to the concrete arithmetic argument. Version 20 retains the previous application proofs; these still use Corollary 4.3. This accurately describes a partially implemented revision, not a failure of the comparison proof.

## 1. Actual outline and section functions

Numbers and pages below are those of the assembled PDF, rather than the numeric prefixes of the source filenames.

| Part | One mathematical job | Subsections and numbered results | Principal dependencies |
|---|---|---|---|
| Abstract; §1, pp. 1–3 | State the problems, examples, and relation to previous work. | §1.1 Related work. No numbered results. | Still organized around Theorem 3.5 and the Miller example. Revision is expressly deferred. |
| §2 Categorical preliminaries, pp. 3–4 | Fix the categories, morphisms, operations, and conventions used in the comparison. | §2.1 Partial maps and restriction idempotents; §2.2 Products, coproducts, and local connectedness; §2.3 Recursion categories. | Restriction categories, ranges, splittings, products, coproduct comparison, Turing morphism. |
| §3 Diagonal comparison and lifted partial conditionals, pp. 4–7 | Turn a lifted target conditional into diagonal avoidance, then derive source inseparability under sufficient hypotheses. | §3.1: Theorem 3.1 comparison; Corollary 3.2 obstruction to lifted separators. §3.2: Lemma 3.3 connected-domain alternative; Proposition 3.4 partial sections; Theorem 3.5 source inseparability. §3.3: Proposition 3.6 lifting from disjoint joins. | §2. The main comparison needs a Turing morphism and the specified partial lift. Local connectedness enters Proposition 3.4 and Theorem 3.5. |
| §4 Internal theories and semantic consistency, pp. 7–10 | Relate categorical generated theories to interpreted ranges and apply the comparison to theorem/refutation domains. | §4.1: Proposition 4.1 interpretation of a sentence theory. §4.2: Theorem 4.2 target and source noncoverage. §4.3: Corollary 4.3 inseparability for every consistent enlargement. | Appendix A, particularly A.6–A.7; the extension of a range functor to restriction splittings; Theorem 3.1. |
| §5 Miller sequences and essential incompleteness, pp. 10–16 | Realize the argument for computation uniform across representations of Miller’s sequence. | §5.1: Lemma 5.1 unanimous computation; Proposition 5.2 the recursion category. §5.2: Lemma 5.3 reduction to cut-index sets; Corollary 5.4 inseparability and separation relative to a fixed representation. §5.3: Proposition 5.5 categorical first-order realization; Theorem 5.6 essential incompleteness for the specified semidecidability class. | Theorem 3.5; Corollary 4.3; Appendix A; the stated Miller property. |
| §6 The syntactic recursion category, pp. 16–28 | Construct the syntactic recursion category and prove that its total restriction splitting realizes Appendix A. | Initial setup: Lemma 6.1 arithmetic computation laws. §6.1: Lemma 6.2 functional search; Lemma 6.3 the regular total category and partial inverses. §6.2: Lemma 6.4 finite membership conditions; Propositions 6.5 and 6.6 syntax and list initiality with parameters. §6.3: Proposition 6.7 free variables and substitution. §6.4: Lemma 6.8 initial derivations; Theorem 6.9 internally generated theories. | Arithmetic coding and uniform provable graph equality; Appendix A’s categorical definitions and closure theorems. The realization proofs remain here, outside Appendix A. |
| §7 Interpretation in models, pp. 28–29 | Interpret program graph formulas in one arithmetic model. | Proposition 7.1: the functor preserves restriction products, coproducts, ranges, and joins. No subsections. | §6’s graph identities. This section does not yet prove soundness of the whole interpreted proof object. |
| §8 A faithful family and theory extension, pp. 29–31 | Assemble all countable model interpretations to reflect graph equality and describe ambient-theory change. | Theorem 8.1 faithful product interpretation; unnumbered commuting square for theory extension. §8.1: Lemma 8.2 complementary-conditionals lift; Corollary 8.3 source inseparability. The ending distinguishes preservation of graph structure from preservation of Turing universality. | Proposition 7.1; completeness and downward Löwenheim–Skolem; Theorem 3.5. |
| §9 Essential incompleteness of arithmetic, pp. 31–35 | Derive ordinary recursive inseparability and essential incompleteness from the numerical recursion category. | Proposition 9.1 numerical categorical realization; Corollary 9.2 essential incompleteness. §9.1 Numeral instances and theory extension: the category `Pair(Rec)`, its theory-extension functor, numeral observations via the faithful family, the complete ambient-theory example, and comparison with Bernardi’s numerical argument. | Theorem 3.5; Corollary 4.3; Appendix A; Lemma 6.1. Part of §9.1 also uses Theorem 8.1. |
| §10 A recursion category from a three-point space, pp. 35–42 | Give a different recursion category and obtain propositional theories and endpoint incompleteness. | §10.1 Local connectedness and lifting. §10.2: Proposition 10.1 endpoint functors and Turing preservation. §10.3: Proposition 10.2 syntax initiality; Proposition 10.3 proof initiality; Theorem 10.4 generated theories and consistency; Theorem 10.5 compatible extensions and endpoint inseparability; Corollary 10.6 essential incompleteness. | Appendix B’s category construction; Appendix A.4 and A.6; Theorem 3.5; Corollary 4.3; `Pair(Rec)` from §9.1. |
| Appendix A Syntax and deductively closed theories, pp. 42–50 | Define categorical syntax and construct the generated theories needed by the applications. | A.1 Categorical hypotheses and notation. A.2: Definitions A.1 syntax and A.2 sentences. A.3: Proposition A.3 admissible substitution. A.4: Definition A.4 rule closure; Theorem A.5 least closed image. A.5: Theorem A.6 first-order theories; Lemma A.7 regular images and ranges. A.6 propositional theories. | Its stated categorical hypotheses and cited literature. No incompleteness argument or numerical realization is imported into it. |
| Appendix B The three-point cosheaf construction, pp. 50–58 | Supply the category, universal object, Turing morphism, and splitting used in §10. | B.1: Propositions B.1 cosheaf equivalence and B.2 regular/extensive total category. B.2: Propositions B.3 partial maps/ranges and B.4 local connectedness. B.3: Lemmas B.5 universal object and B.6 frame. B.4: Theorem B.7 Turing morphism. B.5: Proposition B.8 recursion category and restriction splitting; Corollary B.9 Karoubi completion; Proposition B.10 distinction from numerical recursion and failure of decidable equality on the universal object. | The category of c.e. carriers; the concrete fork diagram and coding described in §10. |
| Appendix C Necessity of section lifting, pp. 58–60 | Show that the lifting hypothesis cannot be replaced by faithfulness, product preservation, or zero reflection. | Proposition C.1, including the example without a lift and the failure of a common upper bound for disjoint morphisms. | Theorem 3.5; numerical recursion with oracle-c.e. domains and ordinary partial-recursive extensions. |
| References, pp. 60–61 | Supply the cited sources. | Thirty bibliography entries. | Verification of every cited external result is outside this organization review. |

There are 54 numbered theorem-like items: 51 results and three definitions. The two items numbered “A.3” are a subsection and a proposition, respectively; they are different numbering sequences, not a duplicate label.

## 2. The dependency chains actually present

The general comparison is already integrated into the retained applications:

\[
\text{Theorem 3.1}\longrightarrow\text{Corollary 3.2},\qquad
(\text{Corollary 3.2}+\text{Proposition 3.4})
\longrightarrow\text{Theorem 3.5}.
\]

Theorem 3.5 supplies the inseparable source pairs. Appendix A and the realization propositions supply the generated theorem subobjects. Corollary 4.3 then yields the concrete incompleteness conclusions in Theorem 5.6, Corollary 9.2, and Theorem 10.5/Corollary 10.6.

The new logical branch is:

\[
\text{Appendix A}+\widehat F
\longrightarrow\text{Proposition 4.1},\qquad
\text{Theorem 3.1}+\text{interpreted consistency}+\text{partial lift}
\longrightarrow\text{Theorem 4.2}.
\]

Its hypotheses and conclusion are stated and proved in §4. No later concrete result in v20 invokes Proposition 4.1 or Theorem 4.2. A whole-source search finds references to `thm:logical-comparison` and `prop:interpreted-theory` only at their declarations; references to `thm:comparison` occur in §§3–4. This does **not** make Theorem 3.1 unused: the first chain above is an actual use. It means that the concrete application of the second chain remains to be written.

## 3. Organization findings and recommended treatment

| Anchor | Finding | Status and rationale | Recommended treatment |
|---|---|---|---|
| Theorem 3.1, p. 5; §3, pp. 4–7 | The new comparison has its own subsection and is the first result of the dedicated general-theorem section. | Adequate. The ordering puts the general result before sufficient lifting hypotheses and applications. KLR §1, points 10–12, supports explaining this progression; it does not require more sections. | Keep §3 intact. A shorter heading, “The comparison theorem,” would be optional, not a necessary correction. |
| Theorem 4.2, p. 9; application proofs pp. 16, 34, 41 | The new semantic-consistency argument has no concrete application yet. | Necessary next implementation step under the approved plan, not an error in the current theorem. The source-consistency applications remain valid as a separate branch. | Write the model/soundness section and the arithmetic partial-proof-search application before claiming that the revised paper realizes that complete chain. |
| Proposition 7.1, p. 29; Theorem 8.1, pp. 29–30 | One-model graph interpretation and all-model faithfulness are adjacent but have different jobs. Neither currently supplies the planned proof-object soundness theorem. | Substantive distinction, not cosmetic categorization. It would be misleading to describe v20 as already containing the plan’s soundness and ultrapower results. | Expand the one-model section with the precise interpretation of syntax and sentence proofs. Keep the all-model comparison for equality reflection and ambient-theory extension, moving it to Appendix D as the plan proposes. |
| Lemma 8.2 and Corollary 8.3, pp. 30–31 | The source-inseparability argument is packaged after all-model faithfulness. Its lifting construction is interpreted model by model; faithfulness is not needed for that argument. | A dependency can be shortened, but the all-model theorem is not thereby pointless. | Move the one-model lifting argument into the model section when revising it, and derive source inseparability there. Move the stronger faithful-family result separately. |
| §9.1, pp. 34–35; equation (16) | The numerical observation identity uses faithfulness; `Pair(Rec)` is later used in Theorem 10.5. | These are actual dependencies. Moving or deleting all of §9.1 as a unit would lose them. | Move the faithful-family observation with the faithful-family appendix. Retain or relocate the definition of `Pair(Rec)` before its cosheaf use. Preserve the complete-ambient-theory example near the discussion distinguishing computational inseparability from a theory’s incompleteness. |
| §5 before §6; pp. 10–16 followed by pp. 16–28 | The Miller application interrupts the path from the abstract internal-theory theorem to its syntactic realization. | Current order is coherent for the old Miller-led paper. It is less direct for the approved comparison/soundness organization. | After the soundness and arithmetic sections are implemented, move Miller after arithmetic, as in the approved plan. Preserve its category construction and all realization proofs. |
| §6, pp. 16–28 | This is the longest main section, but each subsection proves a prerequisite for Theorem 6.9. | Length alone is not a reason to cut it. The functional search, finite membership, parameterized initiality, substitution, and derivation proofs are dependencies. | Retain the full proofs. In the next revision, consistently distinguish the ambient theory from the represented axiom presentation, as the plan’s notation does. |
| Appendix A, pp. 42–50; §4.1, pp. 7–9 | Some definitions recur because Appendix A is self-contained and §4 states the hypotheses of its application. | Justified repetition. In particular, the partial-inverse condition for identifying a regular image with a range must remain at the application. | Keep the complete appendix. Do not replace it with the plan’s abbreviated proof outline or remove dependencies to shorten it. |
| Proposition 9.1, pp. 32–33; Proposition B.2, pp. 51–52 | The regular category of c.e. carriers is established twice. | Optional consolidation; it is not a correctness defect. The diagram-category argument in B.2 is additional and essential. | After the main argument is integrated, B.2 may cite the numerical part of 9.1 and retain its componentwise naturality/descent proof. Keep both if independent readability of Appendix B is preferred. |
| Introduction, pp. 1–3, especially its final roadmap paragraph | It still leads with Theorem 3.5, calls Miller the principal application, and says §3 contains its incompleteness corollary, which is now in §4. | Deferred correction by explicit user instruction. This should not be treated as permission to revise the introduction now. | Correct the roadmap, leading theorem, and application order in the final introduction/abstract pass. |

The placement of Appendix A after the applications is a conventional forward reference, not an unexplained definition gap: §4 and each realization explicitly identify the definitions and results being used. KLR’s discussion in §§4–5 allows definitions to be placed according to the reader’s needs; it does not prohibit such an appendix arrangement.

## 4. Actual paper versus approved plan

| Approved part | Status in v20 |
|---|---|
| General comparison and lifted partial conditionals | Implemented as §3. |
| Internal theory images and semantic-consistency implication | Implemented as §4; includes source noncoverage via preservation of joins. |
| Full categorical syntax appendix | Installed as Appendix A. |
| Syntactic realization | Present as current §6 with full proofs; its notation and placement have not yet been reorganized to the plan. |
| One-model interpretation extended to the total splitting, soundness, ultrapower comparison, and full interpreted-proof soundness | Only the basic graph-interpretation functor is presently in §7. The remaining results occur in the plan, not in the manuscript. |
| Arithmetic application inside the fixed ambient syntactic category, using partial proof search | Not yet implemented. Current §9 proves the numerical source-consistency route. |
| Miller and cosheaf applications after arithmetic | Present with full proofs, but Miller remains before the syntactic and arithmetic sections. |
| Faithful all-model comparison in Appendix D | Not yet relocated; current §8 and part of §9.1 contain it and its uses. |
| Final introduction and abstract | Expressly deferred. |

## 5. Minimal next revision order

1. Revise the present syntactic/model material so the ambient arithmetic theory and the represented axiom presentation remain distinct throughout. Retain the full realization proofs.
2. Complete the one-model interpretation and soundness section, including the plan’s ultrapower construction and the precise limits of what it preserves. The interpretation of code objects and the semantic model supplying validity must have their respective roles stated.
3. Rewrite the arithmetic application around the fixed ambient syntactic category: diagonal-domain representation, partial proof-search lift, Theorem 4.2, then recursive inseparability and essential incompleteness. Retain the numerical realization as a proved comparison.
4. Move the faithful family and ambient-theory extension to Appendix D, together with the material that genuinely uses faithfulness. Preserve `Pair(Rec)` before its later use.
5. Move Miller after arithmetic; retain the cosheaf application and its construction appendix. Check dependencies after the move rather than abbreviating the proofs to match the plan’s shorter outline.
6. Revise the introduction and abstract last, using the results actually present after these changes.

A suitable final order is therefore the approved one: preliminaries; comparison; internal theories; syntactic realizations; model interpretation and soundness; arithmetic; Miller; cosheaves; Appendices A–D. There is no organizational reason to add another general-theorem section between the current §§3 and 4.

## 6. Scope and source consultation

Read the assembled manuscript text, its headings and numbered statements, and the construction/proof passages needed to determine dependencies; checked their numbering and page locations against the PDF and `.aux` file. Read the approved plan’s organization and the proposed model/soundness and arithmetic developments. This is an organization and dependency review, not an independent certification of every mathematical proof or bibliographic claim. No manuscript file was edited and no compilation was repeated.

Consulted the supplied Stanford-report text of Knuth, Larrabee, and Roberts, *Mathematical Writing*, §1, especially points 5 and 10–12, and the definition-placement discussion in §§4–5 (printed pp. 9–12). The specific reordering recommendations above are applications of those principles and of the approved plan; they are not rules prescribed by KLR for this paper.
