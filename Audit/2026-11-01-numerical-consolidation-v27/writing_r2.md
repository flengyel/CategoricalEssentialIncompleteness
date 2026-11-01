# Mathematical Writing closure check

The three findings in `writing_r1.md` are resolved in the inspected source. No further local writing repair is identified.

The reread was limited to the repaired numerical-foundation paragraphs, their Appendix B identification, and the shared §9 carrier/subfunctor convention. The governing source and original scope are recorded in `writing_r1.md`; no whole-paper judgment is made here.

| Previous finding | Verified repair |
| --- | --- |
| Literal target of the restricted partial comparison suppressed | Appendix B explicitly states the canonical isomorphism `Tot(K_rec) ≅ C_rec` before identifying the restricted functor with `F: B_rec → C_rec`. |
| Partial-morphism evaluation and second span introduced implicitly | The shared proof declares `k(x)` as the value of the represented partial function, displays the second span with middle object `B'`, and retains the typed inverse morphisms and all four commuting equations. |
| “Universal arrows” contrary to the author's terminology | The finite-limit paragraph now says “universal morphisms.” |

The revised §9 convention expressly restricts the carrier abbreviation to c.e. subsets, declares that subset and image expressions refer to carriers, and gives component objects and restricted morphisms for a c.e. subfunctor. These declarations preserve the distinction between numerical objects, their carriers and the fork category.

The numerical equivalence still includes its object and morphism assignments, the computable preimage section, normalized partial spans, the composition pullback, and matching domains and values for the naturality comparisons. Appendix B retains its separate natural-descent, probe and extensivity arguments. No assurance phrase or new editorial-process commentary was introduced in these repairs.

A direct source comparison confirms that the first-order proof and proof-code-comparison tail beginning “Choose the variable object” is byte-for-byte identical as text to the version 26 baseline. This observation establishes preservation of that tail, not an independent proof of its mathematics.

**Disposition:** the local writing review passes within its stated scope. No concrete finding remains unresolved. This check did not compile or inspect a new PDF, establish theorem correctness or novelty, or review unchanged sections of the paper.
