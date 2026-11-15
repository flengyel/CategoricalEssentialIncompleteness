# Full Lean replay against manuscript v58

The full WSL verification workflow passed at
`f0e4b78e83ea21e06b7d335bd8b72353ac25502f`. All **1,790 commands passed**, including
**1,784 strict elaborations**. This is a completed
full replay, separate from the earlier 25-command incremental verification
of [Theorem 5.3](V58_ASSOCIATED_INCOMPLETENESS_2026-11-14.md).

The active correspondence has **70 of 77 numbered results proved** and
seven open obligations: 8.9, 8.10, 9.6, 9.8, 10.7, 10.8 and 10.9.
Theorem 5.3 is complete, including arbitrary closed slice extensions, both
directions of closure, consistency and completeness transfer, the full
essential-incompleteness equivalence and final reduction clause. The actual
partial-slice coordinate comparison and full independent statement check
are included in this replay. Manuscript v58 is unchanged.

The run executed the project build, retained statement audit, manifest-selected
statement entry point, every selected V46 producer/check source with strict
elaboration, parser tests and both complete transitive axiom audits. The
current production audit covers **935 modules and 28,620 declarations**;
the retained audit covers **1,274 declarations**. Both axiom
unions are exactly `propext`, `Quot.sound`, `Classical.choice`.

All 2,428 measured inputs stayed unchanged throughout
the run and match the committed source revision. All sixteen dependency
worktrees were clean and pinned at both ends. All 356 imported-source and
four retained manuscript provenance checks passed. The current manuscript's 24 TeX files,
PDF copy, source archive and manifest/correspondence checks passed. The two
unrelated Palomar files remain preserved.

The [machine-readable record](V58_FULL_VERIFICATION_2026-11-14.json) includes
all commands, exit statuses, times, log hashes and source/dependency metadata.
The raw evidence is preserved at `.codex-work/verify-20261114T214424Z-PGfnAE`.
Earlier full and incremental runs remain preserved as records of their own
tested revisions. The remote joint-continuation instructions added during
this replay change only unmeasured documentation. Their 70/77 status agrees
with the tested correspondence. The pending Google Deep Review report was
not supplied or evaluated. Later reporting changes do not alter any measured
Lean, manuscript, dependency, verification script or correspondence-table input.

- Raw verification JSON SHA-256: `3aa2b4d5bba1b559a39105b2ce00de8e78013fc46d472ae4062126927c8a30de`.
- Source snapshot SHA-256: `0425a4ba9904dd334cb347c45d93f9ddc21fd85cd9ad3708b715c33097282b78`.
- Wrapper exit status: 0.
