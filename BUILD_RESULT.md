# Categorical essential incompleteness: build result

## Characteristic arrows and Boolean decisions checkpoint

Verified on 2026-10-28 using Lean 4.35.0-rc2 on Linux x86-64, starting from
`988d958983e716e175b293721aaeea1d03a5666d`. The existing checkout was clean,
and the remote `main` agreed before editing.

- `python3 scripts/verify.py`: PASS.
- Combined entry point: PASS (1892 jobs, including cached dependencies).
- Transitive axiom inspection: PASS for all 47 declarations, retaining every
  previous check. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
- All sixteen dependency revisions and all 356 imported-file records match
  their pins or the two pre-existing recorded patches.
- All three new modules compile without warnings. The two existing imported
  linter warnings remain.
- The scan of all ten project Lean files found no `sorry`, `admit`,
  `axiom`, or `opaque` declarations. No imported source was changed.

`CharacteristicArrows.lean` constructs characteristic arrows of specified
complementary subobjects, proves their two fiber equations and uniqueness,
and proves the coproduct decomposition of an arbitrary arrow to `1 + 1`.
`TwoBoolean.lean` constructs the internal Boolean algebra on `1 + 1`, proves
naturality of its operations on generalized elements, and proves that each
bound copairing into an internal Boolean algebra is a Boolean homomorphism.
`BooleanDecisions.lean` proves `prop:complete-extensions-and-decisions`, both
for an injective bounded lattice map into subobjects and for the existing
domain-to-predicate embedding followed by the subobject identification. It
also excludes represented Boolean decisions under the external diagonal
hypotheses.

The full enriched input construction at the actual separator object `Sep`
and the numerical/arithmetic interpretation remain open. See
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for their precise scope.
The source toolchain and imported provenance are unchanged. The documented
hosted executable-path adapter was used; Palomar Comparator, NanoDa, and
con-ron were not run.

Evidence is retained in [Audit/2026-10-28-decisions](Audit/2026-10-28-decisions/).

## Boolean-presentation checkpoint

Verified on 2026-10-28 using Lean 4.35.0-rc2 on Linux x86-64, starting from
`639edbafe31cbe84122ec532cca1818f3d7257b5`. The existing checkout was clean,
and the remote `main` agreed before editing.

- `python3 scripts/verify.py`: PASS.
- Combined entry point: PASS (1889 jobs, including cached dependencies).
- Transitive axiom inspection: PASS for all 33 declarations, retaining all
  26 previous checks and all eleven original foundation checks. Only
  `propext`, `Classical.choice`, and `Quot.sound` occur.
- All sixteen dependency revisions and all 356 imported-file records match
  their pins or the two pre-existing recorded patches.
- `BooleanPresentations.lean` compiles without warnings. The two existing
  imported linter warnings remain.
- The scan of all seven project Lean files found no `sorry`, `admit`,
  `axiom`, or `opaque` declarations. No imported source was changed.

The new module proves all three clauses of manuscript
`lem:complete-boolean-presentation`: consistency is equivalent to the bound
copairing being monic; completeness is equivalent to its being a regular
epimorphism; and both together are equivalent to its being an isomorphism.
The quotient theorem now also concludes that its bound copairing is not a
regular epimorphism. These are results about actual equalizer subobjects,
regular epimorphisms, and coproducts in a regular extensive category.

The full enriched input construction, the correspondence with decisions, and
the numerical/arithmetic interpretation remain open. See
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for their precise scope.
The pinned source toolchain and imported provenance are unchanged. The
documented hosted executable-path adapter was used; Palomar Comparator,
NanoDa, and con-ron were not run.

Evidence is retained in
[Audit/2026-10-28-boolean-presentations](Audit/2026-10-28-boolean-presentations/).

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
