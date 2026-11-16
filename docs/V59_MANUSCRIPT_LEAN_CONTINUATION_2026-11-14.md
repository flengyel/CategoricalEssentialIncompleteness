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
both complete axiom audits. The later [consistency proof](V59_SIGNED_CONSISTENCY_2026-11-15.md)
proves the PA sentence, formula and sentence image consistency, regular-image
generation comparison and generated signed consistency in the predicate
category. The presentation and its subobject-indexed initial proof family
are constructed. Its 22-command incremental verification includes both
complete axiom audits. The later [diagonal signed-theory assembly](V59_DIAGONAL_SIGNED_THEORY_2026-11-15.md)
completes Lemma 8.9, including the actual split generators, target generated
consistency, free-syntax initiality for arbitrary parameters and every closed
consistent extension. Its 23-command incremental verification includes both
complete axiom audits. The later [arithmetic associated-category proof](V59_ARITHMETIC_ASSOCIATED_CATEGORIES_2026-11-15.md)
completes Corollary 8.10, including arbitrary closed consistent slice extensions,
both split Turing categories, the literal full recursion subcategory and the
specified original arithmetic evaluator. Its 16-command final incremental verification
includes both complete axiom audits. The later [Miller parameterized-deduction proof](V59_MILLER_PARAMETERIZED_DEDUCTION_2026-11-15.md)
completes Lemma 9.6 for arbitrary nullary coefficients and every printed
signature in every parameter slice. Its 16-command incremental verification
includes both complete axiom audits. The later [Miller associated-category proof](V59_MILLER_ASSOCIATED_CATEGORIES_2026-11-15.md)
completes Corollary 9.8 with the actual slice Turing structure, arbitrary
extensions, inseparable domains, Boolean witness and all comparison functors.
Its 22-command incremental verification includes both complete axiom audits.
The later [first-order fork formula proof](V59_FORK_FIRST_ORDER_FORMULA_2026-11-16.md) constructs the initial
formula algebra for every coefficient diagram, with the full numerical
variable carrier and atom-identifying transitions. Its 17-command incremental
verification includes both complete axiom audits. Parameter stability,
variable lists, occurrence/substitution and parameterized finite derivations
remain open in Proposition 10.7. The later [parameterized component proof](V59_FORK_PARAMETER_COMPONENTS_2026-11-16.md)
constructs formula initiality in every numerical parameter slice and fold
uniqueness across arbitrary parameter and atom-label morphisms. Its separate
17-command incremental verification includes both complete axiom audits.
The later [natural parameter fold proof](V59_FORK_NATURAL_PARAMETER_FOLDS_2026-11-16.md)
proves the actual source constructor square, natural folds and initiality
among componentwise natural relative formula algebras for arbitrary target
families, and a canonical constant-family carrier isomorphism. Its separate
23-command incremental verification includes both complete axiom audits.
The later [canonical diagram syntax proof](V59_CANONICAL_DIAGRAM_SYNTAX_2026-11-16.md) constructs ordinary
initiality for the exact canonical two-sort polynomial, with an actual
polynomial isomorphism and algebra-category equivalence. It also constructs
decidable equality for the specified constant numerical-variable diagram.
Its separate 16-command incremental verification includes both complete
axiom audits. Canonical parameter stability, stable variable lists,
occurrence/substitution/sentence constructions and finite derivations remain
open. The count stays 74/77. Resume from the latest report; the WSL recovery
archive is retained as historical evidence.
The 1,798-command full replay below is the earlier baseline; this later batch has separate incremental
verification. The original continuation instructions follow.

Repository: `flengyel/CategoricalEssentialIncompleteness`.
Read `AGENTS.md`, `MANUSCRIPT_CURRENT.json` and
`FORMALIZATION_STATUS_V59.md` before editing. Preserve later local and remote
work. The current manuscript is v59; Theorem 5.3 is complete. The recorded
status is **74 of 77 numbered results proved**, with Proposition 10.7 next.

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
