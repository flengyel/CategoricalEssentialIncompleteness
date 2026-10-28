# Categorical essential incompleteness: build result

## Diagonal and quotient checkpoint

Verified on 2026-10-28 using Lean 4.35.0-rc2 on Linux x86-64, starting from
`08e094d7c3e923eb690b66b5fce5ac85f724b636`. The existing checkout was clean,
and the remote `main` had the same revision before editing.

- `python3 scripts/verify.py`: PASS.
- Combined entry point: PASS (1888 jobs, including cached dependencies).
- Transitive axiom inspection: PASS for all 26 declarations, including all
  eleven original declarations. Only `propext`, `Classical.choice`, and
  `Quot.sound` occur; several new results use smaller subsets.
- All sixteen dependency revisions match; all 356 checked imported-file
  records match their pins or the two pre-existing recorded patches.
- The four new modules compile without warnings. The two existing imported
  linter warnings remain.
- No new `sorry`, `admit`, or axiom declarations; no imported-source changes.

The new proofs cover the external diagonal result, its restriction-idempotent
specialization and inseparability consequence, a conditional parameterized
equalizer factorization, and the Boolean-quotient incompleteness argument with
actual subobject fibers. See [the precise correspondence and remaining
obligations](FORMALIZATION_STATUS.md). The full enriched theorem and its
numerical interpretation remain incomplete.

The hosted executable-path restriction was observed, so the existing adapter
documented in [HOST_BUILD.md](HOST_BUILD.md) was used. The source toolchain,
manifest, `SOURCE_PINS.json`, and `LOCAL_PATCHES.json` are unchanged. Palomar
Comparator, NanoDa, and con-ron were not run.

Evidence is retained in [Audit/2026-10-28-diagonal](Audit/2026-10-28-diagonal/).

## Initial foundations checkpoint

The following records the earlier foundations-only verification on 2026-10-28.

- `lake build CategoricalEssentialIncompleteness`: PASS (1665 jobs, including cached dependencies).
- `lake env lean CategoricalEssentialIncompleteness/AxiomAudit.lean`: PASS for all eleven declarations.
- Every audited declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- All sixteen dependency revisions match the pinned manifest.
- The source-hash check passes for 354 unchanged imported files and two explicitly recorded local patches. The root Lake configuration is project-maintained.

The package, entry point, and interface namespace are named
`CategoricalEssentialIncompleteness`. Imported library names remain unchanged.
The entry point imports the six library roots and the nine Failure of
Composition solution declarations, and checks the concrete arithmetic
recursion-category instance and its Turing evaluator.

The two recorded patches are the evaluator-bridge compatibility repair and
the root-package name in the dependency manifest. The bridge uses the proved
`ConcreteEvaluator.eventualGraph_val` characterization instead of unfolding
the older representation. Its theorem statement is unchanged.

Two existing style warnings remain in `Arith.Feferman.StructuralProof` and
`Arith.Feferman.Specialization`, concerning unscoped linter settings. There
are no build errors. The new entry point has no warning.

The version 16 manuscript PDF and LaTeX source are included unchanged. Their
Git blob hashes match `flengyel/Categorical_Incompleteness` commit
`38c4fba2202bb8c001d1aa353ed48b018592e090`; see `MANUSCRIPT_SOURCE.json`.

Palomar permits this source toolchain and selects con-ron from Lean
4.36.0-rc1 for independent replay. This repository has not undergone Palomar
Comparator, NanoDa, or con-ron replay.

This checkpoint supplies the compiled foundations. The manuscript proves
categorical essential incompleteness; formalization of its central theorem
in Lean remains to be completed.

See [the verification evidence](Audit/2026-10-28/README.md),
[SOURCE_PINS.json](SOURCE_PINS.json), and [LOCAL_PATCHES.json](LOCAL_PATCHES.json).
