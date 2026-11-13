# v57 Section 5 prerequisite formalization, 13 November 2026

The drift check passed and formalization resumed at Lemma 5.1. Proof commit
`04b6acb8876a7faa0bf712e4633f27d8addc9dcf` adds three supporting constructions. The count remains
**67 proved numbered counterparts and ten open obligations**; no additional
numbered manuscript result is marked proved.

## New constructions

- `V46MonoInversesChoice` derives local weak choice from splitting restriction
  idempotents and the printed partial-inverse hypothesis on monomorphisms
  of the total category. The theorem has no range premise.
- `V46SplitProducts` constructs products of arbitrary split objects, their
  partial pairing, restriction and projection equations, joint projection
  extensionality and the universal property on total morphisms. Its product
  data induce the existing restriction operation. Bundling the `PCategory`
  laws remains open.
- `V46PartialMapFunctor` constructs the induced functor on monic partial
  maps from a monomorphism- and pullback-preserving functor. It preserves
  restriction, total morphisms and the partial inverses of monomorphisms.

All three producer modules are imported by the project entry point and the
complete current axiom audit. Their explicit statement checks are imported
by both current statement entry points. The correspondence table identifies
these supporting declarations while keeping Lemma 5.1 and Theorem 5.2 open.

## Verification scope and evidence

The incremental run passed **17 commands**, including ten strict commands:
the six new files, the project entry point, both statement audits and the
complete current axiom audit. It also rebuilt the project and both statement
entry points, checked the retained statement audit and reran the retained
axiom audit. The seventeen selected axiom reports passed.

The complete transitive audits cover **871 current production
modules**, **27,470 current declarations** and
**1,274 retained declarations**. Both axiom unions are exactly
`propext`, `Quot.sound`, `Classical.choice`. All sixteen dependency worktrees
were clean and pinned at the start and end; all 356 imported-source
comparisons passed. The retained manuscript-source provenance comparisons
also passed. All 2,352 measured inputs match the committed proof and
were unchanged through the run.

This is an **incremental verification**, not a new full replay of every
unchanged production file. The full 1,708-command replay at
`45a8a6d017850a3a68fcecd01ad82f5a1a83674a` remains preserved. At resumption,
its 2,346 measured inputs matched the workspace after validating the known
correspondence-reporting delta. The new batch changes eleven measured
inputs: six added Lean files, four import entry points and the correspondence
table. It changes no earlier production proof.

The [machine-readable verification record](V57_SECTION5_PREREQUISITES_VERIFICATION_2026-11-13.json)
records every command, log hash, scope and proof status. Raw evidence is
preserved at `.codex-work/v57-partial-slices-20261113/incremental-verification`.

- Source snapshot SHA-256: `b19a1797703c3cd367392bbcbbea25a973889dbd1fb8db3bd659587adbb854db`.
- Raw verification JSON SHA-256: `a2f59e81939f8894a3baebf1c64ab5a4c19fb696b4494eb035117544d189c565`.

The active manuscript remains v57. Its source, PDF, archive, manifest and
instructions retain their previous bytes. The unrelated Palomar workflow
and declaration notes were preserved.

## Remaining construction

Lemma 5.1 still requires the bundled product and prodominical structure,
the partial slices, their Turing parameterization, the full recursion
subcategory on constant objects and its splitting equivalence. The whole
partial slice is not asserted to be isotype. Theorem 5.2 still requires the
specific postcomposition and pullback functors, both adjunctions, full
faithfulness, properness and the comparison square.
