# Numerical realization: fourth type review

**The scalar-label typing defect is closed. One local description of a comparison map should be aligned with its declared type.** No further mathematical or composability defect was identified in this snapshot.

Reviewed snapshot: `tmp/numerical26/round4/08c-numerical-realization.tex`, SHA-256 `28e6178cc451e2ff0de868c7c43872740d23d8dad74d337db3c96c7bb540378a`, together with the unchanged companion numerical-incompleteness subsection and containing arithmetic source.

## Closed scalar-label comparison

The chosen predicate presentation `C_n(z)` and isomorphism `u_n:J_PA(C_n)≅R_n^syn` are now explicitly named. Its interpreted comparison is

`η_n:C_n(N)≅G_N R_n^syn`,

with scalar source `C_n(N)⊆N`. The forward stored-label map has the type-correct sequence

`widehat(R_n^num) --κ_{m_n}^{-1}--> |R_n^num| --ρ_n--> G_N R_n^syn --η_n^{-1}--> C_n(N)`.

The reverse map is `κ_{m_n}ρ_n^{-1}η_n`. Both directions are computable on their valid carriers, from the declared computations and the representing programs for `u_n` and its inverse. These maps are inverse, and the rule comparison equations imply preservation of premises and conclusions after transporting the chosen predicate rule maps through `u_n`. Tree induction therefore proves validity, conclusion preservation, and the inverse equations for the proof-carrier bijection. No interpretation-preservation of initial algebras is assumed.

## Remaining local wording

At lines 438–440, the description of `ρ_n` still says that re-encoding a tuple or tag “in the predicate presentation” gives its value. The declared codomain of `ρ_n` is the actual interpreted carrier `G_N R_n^syn`; the newly declared scalar predicate carrier is instead `C_n(N)`. The two have now been correctly separated by `η_n` in the formulas. The preceding sentence should use the same distinction.

A precise replacement is: “The finite-product, coproduct, and pullback comparisons for the rule constructions give computable bijections” followed by the existing typed display for `ρ_n`. The following explanation can say that these comparisons match each numerical tuple or tag to the corresponding interpreted rule instance. This is a wording clarification, not a missing additional comparison map.

## Retained checks

All round-2 carrier/object corrections remain closed. The numerical category and both equivalences, finite-limit and image calculations, partial inverses, parameterized syntax and list folds, substitution realization, derivation folds, sentence restriction, and numerical incompleteness application retain the explicit types checked in the preceding reports. The two subsections retain distinct purposes and use Appendix A by reference for the general image/least-theory theorem.

No manuscript file was edited. No Lean verification or whole-paper certification is claimed. A local check of the sentence above after replacement is sufficient to close this report; unchanged proofs need not be reconstructed again.
