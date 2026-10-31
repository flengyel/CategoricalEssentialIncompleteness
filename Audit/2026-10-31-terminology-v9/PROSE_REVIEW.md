# Independent mathematical prose review of v9

Source: `manuscript/essential_incompleteness_via_local_connectedness_v9.tex`.

Final inspected SHA-256: `c71c7a10ba6df6f3c9657a71e7808417d0ce3330c99dede337e89e3668cc4831`. The complete source was read at the earlier integrated version; all subsequently changed passages were inspected directly at this final hash. The earlier changes (the subsection heading, displayed word-code formula, and proof relabeling paragraph) were included in that reading.

## Actual outline

1. Introduction: section lifting, the Miller application, syntactic/model and arithmetic applications, the three-point construction, and related work.
2. Categorical preliminaries: restriction structure, ranges, products and coproducts, local connectedness, and recursion categories.
3. Sections and inseparability: the local lifting theorem, a sufficient lifting condition, and the incompleteness corollary.
4. Miller sequences: computations independent of binary representation, the two strict-cut index sets, and the real-closed-field theory.
5. The syntactic recursion category: formal object terms, their assigned sets and numerical codes, arithmetized program graphs, the quotient category, and comparison with Montagna.
6. Interpretation in models.
7. A faithful family, theory extension, and lifting in the syntactic category.
8. Essential incompleteness of arithmetic, including numeral instances and theory extension.
9. The three-point construction: local connectedness and lifting, component evaluation, and propositional theories.
A. Cosheaf/functor equivalence, total and partial category structure, the universal object and frame, a Turing morphism, and restriction splitting.
B. Formula trees, proof trees and their ranges, the initial proof algebra, and first-order derivations with sentence conclusions.
C. The counterexample to omitting section lifting.

## Resolved wording findings

All three reported distinctions between a restriction idempotent and its set of definition have been repaired. The current wording was inspected directly.

| Final source anchor | Implemented wording | Status |
|---|---|---|
| §8, line 1457 | “their joins are partial identities on unions” | Resolved |
| §8.1, lines 1523–1524 | “These are the domains of definition of the partial identities” followed by the two idempotents | Resolved |
| Appendix C, lines 3228–3229 | “These restriction idempotents are the partial identities on the sets” | Resolved |

The final additional changes were also inspected. Section 4 identifies $d$ as an oracle program index before using it to compute a real. Sections 4 and 8 define $\mathrm{Prf}_T$ as a set of codes of finite derivation trees with sentence conclusions, consistently with Appendix B.4. Section 9 fixes an ambient exponent $m(A)$ for each numerical object and the specified exponents for the components of $V$. Appendix A.3 now gives the domain of $f^\#$ using the source code $\operatorname{code}_{m(Y_j)}$ and entries in $(D_f)_j$; it does not identify that domain with a possibly differently coded $(D_f)^\#$. These changes preserve the indicated object and arrow types.

No further concrete repair remains from this prose review.

## Boundaries checked

The manuscript’s explicit definition of a range functor is retained: it preserves restrictions, ranges, restriction zeros, and binary restriction coproducts. Its consequences for binary joins and complementary pairs are stated immediately afterwards. This review recommends neither changing that definition nor adding its clauses again as theorem hypotheses.

The separation between the metatheoretic term algebra $\mathsf O$, an assigned carrier $|X|$, its numerical coding $\gamma_X$, the numerical variables of PA, and a carrier interpreted in a model is explicit. The Montagna comparison supplies the relationship to the actual-set presentation. No additional elementary arithmetization argument is requested.

In the Miller construction, binary representations, the exact common domain, and the common output are specified before use. The splitting presentation distinguishes its objects, representing partial identities, and arrows restricted to the stated carriers. No undeclared “row” or “support” remains: occurrences of `row` are TikZ layout options.

Appendix B distinguishes concrete derivation trees from values in an arbitrary algebra. Its pullback projections define the functorial action, its algebra structure is named separately from its carrier, and its theorem range is taken in the stated partial-map category. Appendix C distinguishes an arrow’s exact domain from the possibly larger domain of its recursive extension, and gives the functor to partial functions explicitly on numerical objects and arrows.

No further concrete instance of an empty transition, invented object term, or wrong categorical referent was identified in this pass. This is a bounded result, not a claim that no further defect can exist.

## Scope

The complete source was read continuously, including the abstract, introduction, proofs, appendices, and bibliography. The pass applied the already-read Mathematical Writing skill and its Knuth–Larrabee–Roberts source, with Heller’s direct definitions and typed equations as the prose model. It concentrated on definition order, referents, levels of representation, and the integrated changes. It did not independently reprove every result, reverify every bibliographic entry, compile or render the document, run Lean, or perform repository operations. No manuscript edits were made.
