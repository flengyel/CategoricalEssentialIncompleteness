# Iteration domains and computational cosheaves

Date: 29 October 2026.

The new note is [Iteration domains, finite proofs, and computational cosheaves](../../manuscript/archive/iteration_domains_and_cosheaves.pdf)
([source](../../manuscript/archive/iteration_domains_and_cosheaves.tex)).
It continues the repository at dbd8b1ad803c1436ecf6abdc1c4ef1548f7ab4c1.
The preceding 23-page note and 13-page supplement are unchanged.

- [Outline and dependency order](OUTLINE.md)
- [Hostile mathematical review](HOSTILE_REVIEW.md)
- [Mathematical-writing review](WRITING_REVIEW.md)
- [Focused checks by two additional agents](FOCUSED_CHECKS.md)
- [Heller, Lengyel2004, errata, and cosheaf source checks](SOURCE_CHECK.md)
- [Verification and artifact hashes](VERIFICATION.md)

The two reviews are author-side reviews conducted by the drafting assistant
using the requested plugin instructions. They are not independent referee
reports or machine-checked verification.
Two additional agents subsequently checked complementary proof sections;
their scope, findings, and the resulting clarification are recorded separately.

## Results and remaining assumptions

| Result | Discharged | Retained |
| --- | --- | --- |
| Theorem 2.2 | Regularity; equality of restriction ranges and regular images | Split universal product-compatible ranges, weak choice, finite limits of the total category; factoriality is an alternative |
| Theorems 3.1 and 4.1 | The two finite-stage union assumptions in the supplement | Heller's stable finite-length coverage, the stated range/choice structure, finite limits, extensivity, bounded finite arity |
| Corollary 4.2 | Separate finite-stage existence hypotheses | Universal-object dominance and parameter-universal Turing morphism; the supplement's typed Turing-fold proof |
| Theorem 5.3 | Decidable atom equality for consistency of the constructed presentation | Constructed finite-stage syntax/proofs, regular image calculus, disjoint signed atomic domains |
| Theorem 6.4 | All preceding structural and computational hypotheses in one nonnumerical example | Computability is still based on partial recursive component functions; this is not an arbitrary cosheaf completion |

Heller's iteration lemma and the graph union calculation are attributed
reconstructions. The paper does not claim novelty for range failure:
Heller's §10, Example 5 already supplies it. The finite-worklist comparison,
equality-constraint argument, and explicit computational cosheaf application
are the present continuation; no exhaustive priority search was performed.

The next target is a computational cosheaf category on the three-point
space with opens ∅, {c}, {a,c}, {b,c}, {a,b,c}. Its nontrivial cover
requires actual pushout, product, image, and evaluator constructions.
The present note does not complete the Di Paola–Heller program.
