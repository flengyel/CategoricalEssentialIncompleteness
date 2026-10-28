# Categorical essential incompleteness: build result

Verified on 2026-10-28 using Lean 4.35.0-rc2 on Linux x86-64.

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
