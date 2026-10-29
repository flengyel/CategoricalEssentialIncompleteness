# Range completion and the three-point cosheaf space

Date: 29 October 2026.

The new seven-page note is [Range completion and computational cosheaves on a three-point space](../../manuscript/range_completion_three_point_cosheaves.pdf)
([source](../../manuscript/range_completion_three_point_cosheaves.tex)).
It continues repository version 896163707ed3eaa61a30f1d881e8a9f18a3ec0c8.
The preceding three mathematical manuscripts and their PDFs are unchanged.

- [Outline](OUTLINE.md)
- [Hostile mathematical review](HOSTILE_REVIEW.md)
- [Mathematical-writing review](WRITING_REVIEW.md)
- [Focused checks](FOCUSED_CHECKS.md)
- [Source check](SOURCE_CHECK.md)
- [Verification and hashes](VERIFICATION.md)

The reviews apply the requested HostileRefereeGPT and mathematical-writing
plugin instructions. They are author-side assistant reviews with additional
focused checks by three agents, not human independent referee reports or
formal verification. Process remarks are kept outside the mathematical note.

## Results and limits

| Result | What is established | What is not inferred |
| --- | --- | --- |
| §1, established literature | General free range completion; faithful discrete cartesian range completion with universal agreement | Automatic regularity or preservation of computation |
| Lemma 1.1 and Proposition 1.2 | No new total arrows in the discrete completion; with dominance, preservation of the original evaluator forces fullness | Impossibility of every completion or of a replacement evaluator |
| Propositions 2.1–2.2 | Three-point cosheaves as fork diagrams; effective global pushouts; computational regularity, extensivity, ranges, weak choice, word-length coverage | Decidable global quotient equality or pointwise global products |
| Lemmas 4.1–4.2 and Theorem 5.1 | Universal-object dominance, explicit frames, compatible parameter-universal evaluator with exact domains | Automatic range closure of arbitrary generated subcategories |
| Proposition 6.1 and Lemma 6.2 | Genuinely nonnumerical total category, failure of decidable atom equality, binary case distinction | Boolean equality of all atoms |
| Theorem 6.3 | Finite proof algebras and essential incompleteness in this explicit category via the preceding proved theorems | Completion of the general Di Paola–Heller program |

The next construction is a range completion with uniform codes for its
new domains and sufficient total program maps for a compatible evaluator,
together with the required coproduct, iteration, and weak-choice structure.
No new theorem in this continuation has been formalized in Lean.
