# Palomar preparation: editorial review

This report records the review of the manuscript, Lean sources and submission
text during preparation. Preparation is in progress; no candidate has been
fixed and no Palomar intake or registration has occurred.

The v49 manuscript update is committed separately from the unfinished Lean
port. The Lean edits described below are preparation work until their own
verified integration commit. The manuscript-only check does not certify that
port or claim a new full Lean run.

The starting main commit is
`f741d227ff507b2da3150565e1cb9a11477ef6ed`. Its integrated verification
tests proof commit `d437827275d64f6500e6a3bca2ee318420d11edd` against
manuscript v48. Those records are retained for their own source state.

## Sources and order

The governing writing source is Knuth, Larrabee and Roberts,
[*Mathematical Writing*](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf),
especially §§1 and 4–5: define notation before use, give self-contained statements,
write connected prose, and state results without self-assessment. The author's
Došen–Petrić corrections are examples of prose preferences; they do not set
Palomar policy. The Stanford PDF has SHA-256
`646072129e5c74443447d5de1f8343626bcb7cdefb97758721d3ec15d044f5e0`.

The manuscript has been read in the input order of `manuscript/latex/main.tex`,
including its preamble, abstract, introduction, all sections, four appendices,
diagrams and bibliography (22 TeX files). The order is retained: categorical
definitions; comparison and domain criteria; internal theories; syntactic
realization; soundness; arithmetic and its uniform and numerical realizations;
Miller sequences; cosheaves; construction appendices. Definitions precede
their uses. The approved abstract is retained.

The Lean inventory has 2,190 committed files, including the contained source
libraries and checks. The linguistic pass over that inventory is not yet
complete. Searches locate candidates for contextual reading; they do not
establish review coverage. Submission fields and the assembled package will be
recorded here when prepared.

## Editorial decisions

The manuscript uses “full” to distinguish derivations of arbitrary formulas
from their restriction to sentence conclusions, “full” for subcategories and
functors, and “canonical” for comparisons determined by universal properties.
These mathematical uses are retained. “Partial maps” is retained as the
established name of the span construction `Par`.

No mathematical statement has been changed during preparation. Version 49,
dated 9 November 2026, records the terminology edits below. The v48 PDF,
source archive, correspondence and verification records are retained.

| File and anchor | Before | After |
| --- | --- | --- |
| `04-miller-sequences.tex`, Proposition 8.2 proof | “zero maps”; “recursive constant maps” | “zero morphisms”; “recursive constant morphisms” |
| `08d-numerical-incompleteness.tex`, the functor `J_rec` | “zero maps” | “zero morphisms” |
| `09-three-point-space.tex`, universal object and Proposition 9.1 proof | “total map”; “total parameter map” | “total morphism”; “total parameter morphism” |
| `b-three-point-cosheaves.tex`, Propositions B.1–B.3 | “map of pushouts”; “total maps”; “Maps over A+B” | “morphism of pushouts”; “total morphisms”; “Morphisms over A+B” |
| `d-faithful-family.tex`, Theorem D.1 proof | “zero map elsewhere” | “zero morphism elsewhere” |
| `README.md`, Lean status | Numerical, Miller and cosheaf obligations remained | All 62 numbered results have proofs; the v48 verification and the pending port verification are identified separately |
| `README.md`, opening | A summary of the implementation and applications | The approved paper abstract, copied verbatim without its TeX environment, at the author's request |
| `V46ArithmeticNamedProofTranslation.lean`, module documentation | “actual LK2 derivation”; application “still requires” enumeration comparison | Translation by induction on LK2 derivations under axiom admissibility; the axiom-comparison modules instantiate it for PA |
| `V46MillerCanonicalAxiomIncompleteness.lean`, module documentation and `sentence_image_recovery` | “actual literal image”; “genuine point-presentation equivalence”; rhetorical exclusions | Image of sentence words; point-presentation equivalence; the axiom isomorphism and initiality identify the conclusion images |
| `OraclePrefixRecursion.lean`, module heading | “is an actual oracle recursive computation” | “Oracle recursion computes finite oracle prefixes” |

No exported declaration has been renamed so far. The module-system port
exposes the previously private helpers `PCategory.Gen`,
`Subdomain.comp_ambient_idem`, `Subdomain.inverseImageIso_comm`,
`OracleProgram.universalTransition` and `universalTransition_partrec` where
their use in exported definitions requires it. The final declaration map will
give the complete names and any further visibility changes.

The v49 manuscript rebuild succeeded (73 pages), and
`python3 scripts/verify.py --manuscript-only` exited zero. Rendered pages 46
and 61 have been inspected, including the revised coequalizer paragraph and
the pushout and extensivity diagrams. This source gate does not verify Lean.

## Source compatibility

The Palomar rules read on 9 November require module headers and at most 10,000
physical lines in every regular submitted Lean source, with separate limits
of 1,000 lines and 100 KiB for the Challenge. The starting inventory has no
module headers; its largest file has 6,440 lines. Lean 4.35.0-rc2 meets the
current minimum. The port retains that toolchain and the dependency pins.

The port adds public imports, public sections and exposed definition bodies.
Private helpers used by exported definitions require visibility adjustments;
their types and proofs are retained. Compilation and the repository's strict
statement and axiom checks remain required after integration.

Live policy sources are
[the submission standard](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md),
[the protocol](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/docs/specification.md)
and [the agent instructions](https://submit.palomar-registry.org/llms.txt).
The checked-out workflow revision is
`14aa8d6b3c2f14a8540605e37144560b9a00e7e7`;
the policy revision is `28bd48b9b71bbb2a82c718ce761d5a4220ef8e60`.
These will be checked again before the candidate preflight and intake.
