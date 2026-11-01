# Mathematical Writing review of the numerical-foundation consolidation

The consolidation preserves the explanations needed to follow the numerical constructions. It removes the repeated numerical proofs from Appendix B while retaining the fork-specific descent and naturality arguments. Three small repairs remain in the inspected passages; no new mathematical gap is established by this writing review.

Scope: the proposed version 27 of *Logical consequence and essential incompleteness in recursion categories*, compared with `tmp/consolidate27/baseline`. I read the complete numerical-foundation proof and the split first-order statement, the changed Appendix B passages with their surrounding proofs, the shared carrier convention in §9, and the diff. This is not a whole-paper review.

## Actual outline of the changed argument

1. **Numerical category and codings:** define `Rec`, the dimension/carrier category `C_rec`, and the fixed tuple codings.
2. **Structural proposition:** prove the total equivalence using `Q`, `F`, `u`, and `v`; construct finite limits and tagged coproducts; prove regularity using numerical preimage sections; construct mono partial inverses; define the partial comparison functors and prove their quasi-inverse identities.
3. **First-order realization proposition:** retain the syntax, list, substitution and derivation universal-property claims and their existing proof. The structural material now has its own statement rather than sharing that statement.
4. **Appendix B, Proposition `prop:fork-total`:** cite the common numerical result, then prove the component-image, natural descent, finite-probe and extensivity facts for the fork category.
5. **Appendix B, numerical comparison:** cite the constructed `Q_num` before using the numerical total category in the distinction argument.
6. **Section 9 convention:** use the shared dimension/carrier category and declare the subset notation used in the cosheaf construction.

This order is coherent. No additional section or subsection is needed for this consolidation.

## Source consultation

I read the supplied Knuth–Larrabee–Roberts text in `tmp/review_sources/klr.txt`, §1, especially items 10–15 and 26, and the discussion of definition placement in §§4–5. These passages support connected exposition, explanation of introduced variables, consistent notation, restrained indexing and avoidance of unnecessary jargon. The discussion in §4 explicitly allows judgment about nearby definition placement; I have not treated every explanatory clause after a display as a missing definition.

The explicit categorical typing requirement and the author's preference for “morphism” are additional requirements of this project, not claims attributed to KLR. The source file was accessible. This is a source-grounded review, not a provisional substitute for consulting it.

## Findings and repairs

| Anchor | Difficulty | Basis | Repair |
| --- | --- | --- | --- |
| `appendices/b-three-point-cosheaves.tex:594–595`, “Its restriction to total categories is the equivalence F” | The restriction has literal target `Tot(K_rec)`, whereas the displayed `F` has target `C_rec`. The canonical isomorphism has been suppressed at the point where the types are compared. | Project typing requirement; KLR §1, item 14, as applied to consistent categorical notation. Minor, necessary clarification. | State the canonical isomorphism `Tot(K_rec) ≅ C_rec` before identifying the restricted functor with `F`. Suggested text: “Under the canonical isomorphism `Tot(K_rec) ≅ C_rec`, its restriction to total categories is the equivalence `F: B_rec → C_rec`.” |
| `sections/08c-numerical-realization.tex:240–258`, the span criterion and the values `k(kappa_r^{-1}(z))` | `k` is a morphism of the partial-map category and is then evaluated as a partial function. The underlying function is described, but this evaluation abbreviation is not expressly declared. The second middle object `B'` also first occurs in the signatures of the comparison morphisms rather than in a displayed second span. | Project distinction between a morphism and its represented function; KLR §1, items 11 and 14. Minor, necessary clarification. | After the domain/value description, add “Write `k(x)` for this represented partial function.” Introduce the second comparison as the span `C ←[m'] B' →[h'] D` before defining `w` and `w'`. Retain all four commuting equations and both computability arguments. |
| `sections/08c-numerical-realization.tex:111`, “The product and equalizer universal arrows” | The project consistently requests “morphism.” Here the phrase describes the morphisms furnished by the product/equalizer universal properties rather than invoking a separate universal-arrow construction. | Author's terminology instruction, not a mathematical defect or a rule attributed to KLR. Minor local repair. | Replace “universal arrows” by “universal morphisms.” |

No further prose cut is recommended. In particular, retain the actual tagged coproduct/copairing construction, the kernel-pair descent through `s_q`, the explicit normalized span, the composition pullback, and the partial-domain/value checks for the natural isomorphisms. These passages each discharge a mathematical obligation.

## Definition order and notation

- The ambient categories, carriers, tuple codings and domains `D_e` are defined before the partial comparisons need them.
- The two new span legs have explicit source and target objects. Their c.e. carriers and totality are stated.
- The dimension index in the naturality check is `r`, so it does not reuse the monomorphism `m` as an integer.
- The composition proof names the c.e. pullback object `P_{f,g}` and gives the forward and inverse computations. The naturality proof compares both domains and values, rather than values alone.
- The names `u` and `v` are extended from the total comparison to the same components on the partial categories. The componentwise explanation makes that reuse intelligible; no extra family of names is needed.
- The new §9 convention declares how subset notation abbreviates dimension/carrier objects and how membership notation is read. No new undefined terminology is introduced by it.
- No instances of “genuine,” “genuinely,” “bona fide,” “actual,” or a replacement assurance were found in the inspected changed passages. No editorial or review-process commentary was found there.

## Retained distinctions

The numerical surjection section is a morphism in `C_rec`. Appendix B still proves that componentwise descent is natural by its cancellation equation. It does not assume a natural family of the numerical sections. Its probe argument and extensivity proof remain. The first-order universal-property proof remains separate from the numerical structural proof and is not replaced by a claim that regular equivalences preserve arbitrary initial algebras.

## Disposition and limits

Make the three local wording/typing repairs above, then recheck those sentences and their displayed types. No broader reorganization or compression is warranted by this review. I did not alter manuscript files, compile the document, inspect a new PDF, re-prove the first-order realization, assess novelty, or review unchanged applications. Those activities are outside this local writing review.
