# Outline and assessment against the Di Paola–Heller program

The review examines the nine-page note at commit `a9da9ee538edbf4a57e4469185f014aa88c5daf8`. The actual outline was supplied to the Hostile Referee plugin, together with the full manuscript and the original Di Paola–Heller paper. The Mathematical Writing plugin was applied separately to the complete source, with particular attention to non-mathematical and editorial-process remarks.

## Files

- [OUTLINE.md](OUTLINE.md): the existing section order, mathematical functions, results, and dependencies.
- [HOSTILE_REVIEW.md](HOSTILE_REVIEW.md): the adversarial assessment of whether the construction establishes the intended intrinsic connection between formal systems and categorical recursion.
- [PROGRAM_SOURCES.md](PROGRAM_SOURCES.md): primary-source anchors distinguishing the historical program from stronger or unsupported demands.
- [DEPENDENCY_CHECK.md](DEPENDENCY_CHECK.md): an independent check of the arguments and their actual hypotheses.
- [MATHEMATICAL_WRITING_REVIEW.md](MATHEMATICAL_WRITING_REVIEW.md): the complete-source prose assessment, definition-order check, and proposed local wording changes.

## Assessment

The confirmed limitation concerns integration: the separation contradiction works for domains satisfying the representation equations without using deductive closure or a Turing morphism. The category of presentations organizes closures, but does not include the negative and substitution operations later supplied in §4. The arithmetic realization verifies the representation equations from a classical definability hypothesis; the note does not construct that relationship intrinsically for a general class of algebraic formal systems.

These facts do not refute the conditional theorems. In particular, the representation condition is not merely a restatement of incompleteness, and the restriction to computable morphisms and domains is consequential. The original Di Paola–Heller paper explicitly treats definability-to-inseparability as a target form and permits diagonal arguments. The reviews therefore distinguish an unestablished claim of the stronger integration from a mathematical error in the displayed implication.

## Manuscript change and verification

The writing review found no LLM-facing instructions, drafting history, or review-process remarks in the note. The abstract now explicitly says that the **extensions** are computably enumerable, while the base theory need not be. This makes its quantifiers agree with Corollary 5.2. The four source lines containing that sentence are the only manuscript change; theorem statements and proofs are unchanged. Optional wording proposals remain recorded in the review.

The revised source was compiled with `latexmk -pdf -interaction=nonstopmode -halt-on-error`. The final log has no unresolved references or citations and no overfull or underfull boxes. All nine rendered pages were visually inspected. No Lean source was changed, and no Lean build or axiom-audit claim is made for this review.

Revised LaTeX SHA-256: `7496dae90192e56e155d1c24b1eeae1d78a12b45f5832afe87f8a32ffde2b3d7`.

Revised PDF SHA-256: `fc955874508533ed9095d47868982da58455d014a9510b912d6b904fb467a772`.

The reviews retain the original commit as their examination target. Their original abstract finding is resolved by the sentence change recorded here; their structural findings concern unchanged mathematics. Editorial reports and outlines are kept outside the mathematical note.
