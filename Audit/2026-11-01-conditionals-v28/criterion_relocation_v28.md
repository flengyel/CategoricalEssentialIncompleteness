# Complementary conditionals and the separate recursion-category note

The paper now proves its application results using explicit complementary conditionals. The general criterion using target sections has been moved to a revised version of the existing note `LOCOct10f`, in `flengyel/notes`. The original dated source and PDF are preserved unchanged. All logical applications and realization proofs remain in the paper.

## The paper, version 28

*Logical consequence and essential incompleteness in recursion categories*, version 28, 1 November 2026, has 77 pages. Appendix A's standalone export has 10 pages and matching version-28 metadata; its mathematical content is unchanged.

The comparison theorem remains Theorem 3.1, followed by Corollary 3.2 on lifted separators. New Corollary 3.3 states the consequence used by the applications: if every complementary source pair `c,c'` on `U` admits a total morphism `ell_c:U -> U+U` with `ell_c c=i_1 c` and `ell_c c'=i_0 c'`, then the comparison pair is inseparable, under the stated nonzero and target join-preservation hypotheses.

The proof derives the two summand inverse-image equations by range agreement after `[c,c']`. It then applies Corollary 3.2. The retained disjoint-morphism-join proposition supplies such source conditionals when those joins exist. It no longer invokes the removed local-connectedness theorem.

| Application | Conditional used |
| --- | --- |
| Syntactic category and model-family comparison | The source program already constructed in Lemma 6.2; its interpreted graph has the required tagged branches. |
| Ordinary numerical recursion | Parallel membership search for two disjoint c.e. domains covering the carrier. |
| Miller sequences | One oracle program runs the two membership computations in parallel. The domains and selected output are independent of the representation. The compactness/unanimity proof remains necessary for the Turing morphism. |
| Three-point cosheaves | For complementary domain inclusions `m:C -> V` and `m':C' -> V`, the copairing `q=[m,m']` is an isomorphism. The conditional is `[i_1 m,i_0 m']q^{-1}`. Its inverse and naturality are explicitly proved. |
| Cosheaf endpoint theories | Total recursive conditionals in the full numerical subcategory, with the specified endpoint Turing morphism. |

The direct syntactic arithmetic and uniform-independence proofs already avoided local connectedness and remain unchanged. The finite-probe proof of cosheaf local connectedness remains in Appendix B. Appendix C remains as a counterexample to omitting the lift in the general comparison theorem; its statement now identifies the relevant hypotheses explicitly.

The abstract and introduction received only the factual and reference repairs required by the moved theorem and new criterion. Their final broader revision remains deferred.

## The note and `LOCOct10f`

The dated manuscript *Locally connected recursion categories*, revised 10 October 2026, already contains the required criterion, its supporting section results, a disjoint-join sufficient condition, the lifting counterexample, and a separate noncomplementation theorem. It is therefore the source for the revised note, rather than an unrelated additional manuscript.

The preserved originals have the following hashes:

| Original | SHA-256 |
| --- | --- |
| `LOCOct10f.tex`, 46,123 bytes | `039000cafbe3636ae501125d403e8fe15d42effe1c37580346d108a5bec32aab` |
| `LOCOct10f.pdf`, 450,112 bytes, 12 pages | `571ca90d47fdf42eec36b0a57c7b37ab163d8ae8af8ce3bb8c2f7fe1927dd6b5` |

The revised note is *Ranges and inseparability in recursion categories*, version 1, 1 November 2026, 13 pages. It retains all 18 numbered claims from the dated source, including the noncomplementation theorem and counterexample. The acknowledgements and bibliography remain unchanged.

Preparing the note exposed a stronger argument under its existing inverse-image join hypothesis. For total `theta,theta':Y -> X+X`, intersect the two pairs of summand inverse images to obtain four restriction idempotents `delta_ij` whose join is `1_Y`. Equality after `nabla_X(alpha+beta)` implies equality after `alpha+beta` on each piece. Range agreement then proves the required equality globally. Splitness extends the test to partial morphisms; weak choice supplies the section. Local connectedness is not used.

The inseparability proof likewise uses the weak-Turing index identity, the typed coproduct comparison `chi`, and the equation `HE=sE`. The exchanged inverse images are equal and disjoint; total inverse-image preservation of their complementary join gives the contradiction. The theorem retains splitness and weak choice and does not assert minimal hypotheses.

The note is self-contained and does not depend on the current paper for its proof. Its source and PDF, together with the unchanged dated originals, are placed directly under `recursion_categories/` in `flengyel/notes`, following that repository's conventions.

## Review and verification

Independent agents applied the HostileRefereeGPT and Mathematical Writing skills and checked explicit types and dependencies. The writing review consulted the supplied Knuth–Larrabee–Roberts text. The paper reviews cover the new corollary, its concrete applications, and necessary statement/reference repairs. The note reviews cover the changed section and inseparability proofs and affected uses, with the complete dated and revised documents available for context. They do not claim a new independent verification of every unchanged literature result.

The paper's local findings concerned the ambient category for the Miller conditional, the explicit range-functor assertion in Appendix C, exact total inverse-image hypotheses, the reference to the actual lifting premise, and the scope of the introductory join statement. All were repaired. The note's explicit typing of total test morphisms was also completed. No required issue remains in those scoped reviews.

All three revised PDFs compile with no undefined references, undefined citations, or overfull boxes. The rendered changed proofs, application paragraphs, version displays and note transitions were inspected. The source archive contains the final modular bytes and passes its ZIP integrity check.

Direct comparisons preserve the complete first-order realization sources, indexed families, numerical code comparison, model soundness and ultrapower arguments, and the later Miller and cosheaf logical constructions. The original `LOCOct10f` bytes are preserved exactly. No Lean source was changed or tested.
