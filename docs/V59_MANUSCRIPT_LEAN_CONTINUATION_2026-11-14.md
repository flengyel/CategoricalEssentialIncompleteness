# Manuscript v59 and Lean continuation

Continuation update: the canonical positive-leaf assignment, numerical
extraction and common finite atom valuation are constructed and verified.
See [the proof report](V59_SIGNED_DERIVATION_FINITE_SUPPORT_2026-11-14.md) and its record.
The later [Boolean formula valuation](V59_BOOLEAN_FORMULA_VALUATION_2026-11-14.md) has its five constructor equations,
five schemes, both inference rules and signed-atom values in every PA model.
Its 19-command incremental verification is separate from the full replay.
The later [parameterized substitution proof](V59_PARAMETERIZED_SUBSTITUTION_2026-11-15.md)
proves admissible-substitution invariance, including the full Option failure
equation, and completes all seven logical schemes. Its 25-command incremental
verification is separate from the full replay. The later
[internal truth proof](V59_INTERNAL_TRUTH_2026-11-15.md) constructs the coded Pi-one invariant and
excludes contradictory internal signed derivations in every PA model on a
single common support. Its 23-command incremental verification includes
both complete axiom audits. Continue with the PA theorem, generated-theory
consistency, regular-image axiom comparison and final assembly.
Lemma 8.9 remains open; the count stays 70/77. The 1,798-command full replay
below is the earlier baseline; this later batch has separate incremental
verification. The original continuation instructions follow.

Repository: `flengyel/CategoricalEssentialIncompleteness`.
Read `AGENTS.md`, `MANUSCRIPT_CURRENT.json` and
`FORMALIZATION_STATUS_V59.md` before editing. Preserve later local and remote
work. The current manuscript is v59; Theorem 5.3 is complete. The recorded
status is **70 of 77 numbered results proved**, with Lemma 8.9 next.

The [full v59 replay](V59_FULL_VERIFICATION_2026-11-14.md) passed all 1,798
commands, including 1,792 strict elaborations and both complete transitive
axiom audits, at `8df18834734179186459d3c4c34d4c0cf20b6194`. The
[construction report](V59_FINITE_SUPPORT_2026-11-14.md) records four new
producer/Checks pairs for finite support and internal induction. Their
completion does not prove Lemma 8.9.

The Google review has been supplied. Its original text and the independent
assessment are in `docs/reviews/GOOGLE_V58_2026-11-14/`. The alleged
partial-monomorphism typo is absent from the reviewed v58 source and PDF:
the consequent already restricts p. Lean has the same correctly typed
definition. The global-point and uniform-family comments are explanatory
suggestions, not established defects. The confirmed publisher line break
is corrected in v59. All mathematical text, statements and proofs are
unchanged. The phrase “without local connectedness” belongs to the report;
it is absent from the manuscript. Do not add it as a disclaimer.

Continue from the manuscript outline and the actual Lean statements.
`docs/V58_MANUSCRIPT_LEAN_CONTINUATION_2026-11-14.md` retains the detailed
mathematical tasks and verification conventions; its pending-review section
is superseded by the supplied report and assessment. Theorem 5.3 must not
be reopened by copying an earlier status. Keep both directions of its
equivalence and its quantifier over arbitrary closed slice extensions.

## Remaining results

| Result | Construction |
| --- | --- |
| Lemma 8.9 | Positive supports on actual signed derivations; internal Boolean soundness and PA-provable consistency; essential incompleteness of the specified generated theory. |
| Corollary 8.10 | Apply the associated-category theorems after Lemma 8.9, with the full extension quantifier and Boolean witness. |
| Lemma 9.6 | Miller syntax and finite-derivation initiality for the stated arbitrary coefficients in every parameter slice. |
| Corollary 9.8 | Miller associated-category application. |
| Proposition 10.7 | First-order fork syntax and finite-derivation initiality in every parameter slice. |
| Proposition 10.8 | Natural embedding and erasure, conservativity, consistency, essential incompleteness and endpoint conclusions. |
| Corollary 10.9 | First-order fork associated-category application. |

Use the printed hypotheses. Generation uses initial algebras only for axiom
subobjects; arbitrary presentation morphisms first pass through their regular
images. Retain true as the second coproduct injection and universal
quantification as the second projection. Distinguish standard indices from
arbitrary internal elements and internal finite lists. Keep editorial and
review commentary outside the article.

Preserve the pinned Lean toolchain, dependencies, source-provenance checks
and designated isolated Palomar placeholders. Production proofs and their
transitive dependencies must use only `propext`, `Quot.sound` and
`Classical.choice`. Add independent statement checks and full transitive
coverage for each new producer. Do not replace a construction by its
conclusion as a hypothesis.

Run the parser tests and manuscript gate, then the serial, locked verification
workflow in `scripts/verify-wsl.sh`. Distinguish successful incremental checks,
interrupted attempts and a completed full replay. Update a numbered row only
after all clauses of the printed result have proved counterparts. Preserve
the v58 artifacts identifying the reviewed version.

Commit verified batches promptly to `main`, push without force, preserve
concurrent changes and verify the live remote commit and selected version.
