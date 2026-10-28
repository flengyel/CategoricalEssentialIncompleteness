# Combined development: build result

Verified on 2026-10-28 using Lean 4.35.0-rc2 on Linux x86-64.

- `lake build CombinedDevelopment`: PASS (1665 jobs, including cached dependencies).
- `lake env lean CombinedAxiomAudit.lean`: PASS for all eleven declarations.
- Every audited declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- All sixteen dependency revisions match the pinned manifest.
- 355 imported files remain byte-identical to their recorded Git blobs; one imported proof file has an explicit, hash-checked compatibility patch. The Lake configuration adds the combined target.

The combined root imports all six maintained library roots and the nine Failure of Composition solution declarations. Its two additional declarations check the concrete arithmetic recursion-category instance and its Turing evaluator.

The initial cold build exposed one incompatible simplification in `Palomar/EvaluatorBridge.lean`. The repair uses the proved `ConcreteEvaluator.eventualGraph_val` characterization instead of unfolding the older `mkSigma` representation. The theorem statement is unchanged. The initial failure, exact diff, focused repair build, and successful combined build are retained.

Two existing style warnings remain in `Arith.Feferman.StructuralProof` and `Arith.Feferman.Specialization`, concerning unscoped linter settings. There are no build errors. The new combined module has no warning.

Palomar currently permits this source toolchain and selects con-ron from Lean 4.36.0-rc1 for independent replay. This combined tree has not undergone Palomar Comparator, NanoDa, or con-ron replay. The toolchain and checker requirements are recorded separately.

This establishes a compiled common foundation. The new version-16 definability-algebra and incompleteness theorems remain to be formalized.

See `build-logs/verification.json`, `build-logs/combined-build.log`, `build-logs/axiom-audit.log`, `SOURCE_PINS.json`, and `LOCAL_PATCHES.json` for the exact evidence.
