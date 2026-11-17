# Mathematical review of manuscript v59 and revisions in v60

The categorical characterization in Corollary 4.8 and transfer theorem in Theorem 5.3 survived the proof review. The false theorem identified is Theorem 4.1 of the 2006 technical report: Proposition C.1 of the present manuscript is a counterexample under its printed hypotheses. The manuscript also has a formal correspondence discrepancy at Theorem 5.3. The mathematical proof applies to two calculi, while the verified declaration takes a first-order presentation.

**Reviewed edition.** *Logical consequence and essential incompleteness in recursion categories*, v59, 14 November 2026. [Reviewed PDF](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/7fd727f411653c8ce0336ef2f9280c5b978fc5a7/manuscript/logical_consequence_and_essential_incompleteness_v59.pdf). The reviewed source and Lean snapshot are pinned to `7fd727f411653c8ce0336ef2f9280c5b978fc5a7`. Version 59 retains the numbered statements and mathematical text of the submitted v58. The [previous review assessment](../GOOGLE_V58_2026-11-14/assessment.md) concerns that submission. This is an author-side review.

[Actual outline of v59](outline.md) · [Proof checks by numbered result](proof-checks.md) · [Correspondence for v60](../../../FORMALIZATION_STATUS_V60.md).

**Subsequent Lean proof.** After the review, Proposition 10.8 was formalized, including conservativity, consistency, internal essential incompleteness, and incompleteness for every consistent c.e.-axiomatized extension of either endpoint theory. At that commit the outstanding cases in the v60 correspondence are the standalone propositional case of Theorem 5.3 and Corollary 10.9. [Proof commit](https://github.com/flengyel/CategoricalEssentialIncompleteness/commit/f5176d08e6a7aed7a59d80432cc453eb947f18f3).

## (A) Kill-shots / hard blockers

**False earlier theorem.** In Lengyel, *Locally connected recursion categories* (2006), Theorem 4.1, pp. 11–12, a range functor into a split locally connected target with coproducts, zeros and weak choice is claimed to suffice for inseparability of the two summand inverse images of the diagonal. The proof produces a section in the target and then takes a Turing index for it in the source. Those two operations take place in different categories.

**Counterexample.** Proposition C.1, v59, pp. 81–84, uses a category whose partial numerical functions have an ordinary partial recursive extension and a domain c.e. relative to the halting set. The forgetful functor to partial functions preserves the indicated operations and is faithful. In its target each restriction idempotent splits through its domain, singletons are jointly epimorphic connected domains, and partial injections have partial inverses. The source Turing morphism is in particular weak Turing. Its diagonal pair has a separator consisting of the partial identities on a nonrecursive set decidable in the halting set and on its complement. The corresponding total conditional would decide that set, whereas every total source morphism is ordinary recursive. Thus the earlier conclusion fails. This counterexample concerns the functor assertion of Theorem 4.1 specifically. Manuscript Theorem 3.1, pp. 6–7, obtains its index only after a source lift is given. Version 60 credits the earlier construction and records the counterexample at its proof. [2006 report and bibliographic record](https://academicworks.cuny.edu/gc_cs_tr/277/).

No counterexample to a numbered theorem of the reviewed manuscript was found. The individual proof checks below give the scope of that finding.

## (B) Major weaknesses

| Anchor in v59 | Finding and evidence | Disposition |
| --- | --- | --- |
| Abstract, p. 1, §§1 and 4.6, pp. 1–3, 13–15 | The abstract gives a sufficient reduction criterion, mentions generation and Galois connections, and omits the adjunction for the free first-order theory of a pair and the converse criterion. The latter produces a complete extension from any separator. | The v60 abstract and opening paragraphs state the free construction, its consistency condition, Theorem 4.7, Corollary 4.8 and the independent content of Theorem 5.3. |
| Related work, pp. 3–4, Corollary 4.8 | The categorical diagonal pair and the operation of adjoining positive and negative assertions both have antecedents. The numerical equivalence for a theory built over Jan uses c.e. sets and essential undecidability. The manuscript ranges over subobjects of an arbitrary parameter object and closed internal extensions. | Added the 2006 report, Cockett 7.8 and the numerical comparison. The related work also distinguishes Joyal's arithmetic-universe results and Montagna's comparison of syntactic and numerical recursion categories. The review establishes no priority claim for the general theorems. |
| §5, pp. 15–17, and v59 Lean row 5.3 | The section fixes either a propositional or a first-order system. The checked transfer theorem takes `P : FirstOrderPresentation V`. The checked quantifiers over closed slice extensions are correct. The pure propositional system in Appendix A.6 has three logical schemes, no unary rule and modus ponens. No check identifying its generated theories in the base and slices with those of the cited declaration was found. | The v60 table records first-order coverage of 5.3 and the outstanding propositional specialization. The first-order applications continue to use the verified theorem. |

## (C) Minor issues

| Anchor in v59 | Difficulty | Revision |
| --- | --- | --- |
| Corollary 4.8, pp. 14–15 | The passage from complementary domains to a total Boolean morphism is compressed. This is precisely where a set-theoretic characteristic function could be smuggled into the proof. | Define the Boolean object at this use. The copairing of the two complementary subobjects is monic by extensivity and regular epic by its image. Its inverse gives the required morphism by copairing the two constant values. |
| §5.3, p. 16 | The constant-family functor on partial morphisms is said to preserve finite products. | Specify finite restriction products. The functor on total morphisms preserves ordinary finite products. |
| §2.2, p. 5 | Preservation of joins uses zeros, coproducts and ranges. The term “range functor” has a weaker conventional meaning in the range-category literature. | Attribute the stronger convention at its definition. |
| Appendix A.1, pp. 67–68 | The calculation of Boolean identities lists summands again after giving the operations and their table. | Prove the equations of morphisms by composing with the jointly epimorphic coproduct injections of the relevant power of the Boolean object. |

The exposition follows the original order of the construction and its prerequisites. The changes to the opening apply Knuth, Larrabee, and Roberts, *Mathematical Writing*, §1, especially points 10–13 on connecting formulas, motivation, and what a reader can learn by skimming. The theorem and quantifier checks are mathematical judgments independent of those editorial principles. [Stanford report](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf).

## (D) Cross-section consistency failures

The correspondence discrepancy in (B) is the one confirmed discrepancy in the stated scope of the main results. Three other objections have mathematical answers.

1. In Appendix A.5 and §4, the conclusion morphism factors through its regular image. The finite-rule functor preserves regular epimorphisms, so the algebra descends to that image. Initiality makes the image the least closed subobject. This argument works without an external set of proofs or a collection of all subsets. Initiality is required for axiom subobjects.
2. In Theorem 5.3 evaluation at a logical theorem is pullback along a specified morphism into the base of the slice. The proof transports a closed formula subobject and its rule algebra. It does not assume that arbitrary families are constant or that equality of subobjects can be tested on global points.
3. Numerical carriers, sets of codes, models, oracles and ultrafilters occur in the specified realizations. In the three-point example, the proof checks the naturality of folds, including their domains. A valuation proving consistency at one component need not define a natural valuation of the entire diagram. Intersection is computed componentwise, which is sufficient for that proof.

## (E) Acceptance conditions

The abstract must state the consistency condition and preserve both directions of the main equivalences. The proof of Corollary 4.8 must produce a morphism of the stated category. A comparison using a target conditional must identify its source lift. The revised source meets these three conditions. The next condition for claiming a **complete Lean counterpart to the full printed 5.3** is a checked specialization to the standalone propositional calculus, with its closure subobjects and all consistent closed slice extensions. For a **complete formalization of the paper**, Proposition 10.8 and Corollary 10.9 also require proofs at the reviewed snapshot.

## (F) Not checked / uncertainty log

The review covered the compiled v59 source, all 77 numbered results, three definitions, and the main unnumbered constructions. The theorem-by-theorem notes distinguish reading the Lean statements from checking the scope recorded in the correspondence. Primary-source comparison concentrated on the antecedents of the main claims. It did not establish priority across the entire literature or independently reprove results imported from the cited works.

The strongest confirmed failure is the earlier report's Theorem 4.1. The strongest remaining formal uncertainty concerns comparison with the standalone propositional closure operator in §5.3. The mathematical proof does not depend on a hypothetical encoding into the first-order calculus. No fresh kernel or axiom replay was performed for this manuscript-only revision. The project manuscript verifier passed on the rebuilt 87-page PDF, the 24 TeX inputs, the source archive and the selected correspondence table. Separate byte comparisons matched all 77 numbered result statements and three numbered definitions to v59. The final LaTeX log had no undefined references or citations, duplicate labels, or overfull boxes. The assessment of the printed proofs is independent of the outstanding Lean constructions. A claim of complete formal coverage would be premature.
