# Categorical essential incompleteness: build result

## Numerical categories and support comparison checkpoint

Verified on 2026-10-28 using Lean 4.35.0-rc2 on Linux x86-64, starting from
`c56b783a858087f3b77f6420fd2469e9f28094e6`. The checkout was clean and the
remote `main` agreed before editing.

- `python3 scripts/verify.py`: PASS.
- Combined entry point: PASS (1913 jobs, including cached dependencies).
- Transitive axiom inspection: PASS for 152 declarations, retaining all 113
  previous audits. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
- All sixteen dependency revisions and all 356 imported-file records match
  their pins or the two pre-existing recorded patches.
- All seven new modules compile without warnings. The two existing imported
  linter warnings remain.
- No imported source or dependency pin was changed.

The checkpoint constructs the numerical restriction category, including zero
morphisms and nontriviality, and identifies its domain lattice with c.e.
supports. Complementary domains on `ℕ` are exactly recursive sets. The
arbitrary-PER category uses quotient tracker arrows, and the functor from
total numerical arrows to equality PERs is proved full and faithful.

Support inclusions are genuine categorical subobjects. Their order and
equality reflect support inclusion and equality. The inverse-image square
satisfies the full pullback universal property and agrees with restriction
inverse image. Dovetailing proves that c.e. support unions are least upper
bounds among all categorical subobjects. For disjoint supports, absence of a
complementary-domain separator is equivalent to recursive inseparability.

This establishes the support comparison in part (ii) of
`thm:integration-essential-equivalence`. The next construction is numerical
binary products and their preservation by `J`. Remaining PER regular/extensive
structure, the bounded-lattice packaging, and the syntax/provability and
arithmetic comparisons are open; see [FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md).

The documented hosted executable-path adapter was used. Ordinary Debian/WSL2
builds do not need it. Palomar Comparator, NanoDa, and con-ron were not run.
Evidence is retained in
[Audit/2026-10-28-numerical-supports](Audit/2026-10-28-numerical-supports/).

## Global comparison and categorical theorem checkpoint

Verified on 2026-10-28 using Lean 4.35.0-rc2 on Linux x86-64, starting from
`68d5d9cb07e2bf63f693ea20401ed335a7807357`. The existing checkout was clean,
and the remote `main` agreed before editing.

- `python3 scripts/verify.py`: PASS.
- Combined entry point: PASS (1906 jobs, including cached dependencies).
- Transitive axiom inspection: PASS for all 113 declarations, retaining all
  83 previous checks. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
- All sixteen dependency revisions and all 356 imported-file records match
  their pins or the two pre-existing recorded patches.
- All six new modules compile without warnings. The two existing imported
  linter warnings remain.
- The scan of all twenty-four project Lean files found no `sorry`, `admit`,
  `axiom`, or `opaque` declarations. No imported source was changed.

The global comparison constructs the ordinary total-arrow category, its
equivalence with global total hom-objects, and the bounded lattice comparison
between global domain points and ordinary restriction idempotents. It proves
compatibility with products and actual restriction inverse image. The internal
section supplies the external representation equations through the explicit
chosen-product isomorphism.

The natural predicate identification along `J` gives a genuine natural
presheaf isomorphism and a natural injective bounded lattice map into actual
subobjects. `categorical_essential_incompleteness` and
`categorical_boundCopair_not_regularEpi` prove the two conclusions of
`thm:categorical-essential-incompleteness`, using ordinary nontriviality,
represented restriction domains, and the internal section. The decision
equivalence and Boolean-decision obstruction are also specialized along `J`.

The input is the restriction, product, zero, lattice, predicate, and section
data of a definability algebra. The additional recursion and indexing data are
unused in this proof; a single record bundling the entire algebra is not yet
provided. Product preservation by `J` is retained in the principal theorem,
although the quotient argument uses only its identification component at `S`.
The numerical/PER and arithmetic comparisons remain open. See
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for the exact scope.

The source toolchain and imported provenance are unchanged. The documented
hosted executable-path adapter was used. Palomar Comparator, NanoDa, and
con-ron were not run.

Evidence is retained in
[Audit/2026-10-28-global-comparison](Audit/2026-10-28-global-comparison/).

## Enriched restriction checkpoint

Verified on 2026-10-28 using Lean 4.35.0-rc2 on Linux x86-64, starting from
`ea86f7d8689bcee9594ea11bd976d2265d4b76d3`. The remote `main` was inspected
before editing. The prior transient checkout was unavailable; its text sources
were restored at that exact revision and checked against their Git blob hashes.

- `python3 scripts/verify.py`: PASS.
- Combined entry point: PASS (1900 jobs, including cached dependencies).
- Transitive axiom inspection: PASS for all 83 declarations, retaining every
  previous check. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
- All sixteen dependency revisions and all 356 imported-file records match
  their pins or the two pre-existing recorded patches.
- All four new modules compile without warnings. The two existing imported
  linter warnings remain.
- The scan of all eighteen project Lean files found no `sorry`, `admit`,
  `axiom`, or `opaque` declarations. No imported source was changed.

`EnrichedRestriction.lean` constructs the actual domain equalizers and
totality pullbacks and proves their generalized-point descriptions.
`EnrichedTotals.lean` derives internal total composition and binary products
from the restriction-product equations. `EnrichedDomains.lean` constructs
the partial and total domain inverse-image actions, proves the required
structural laws, and instantiates the internal separator factorization. It
also connects nontriviality of the enriched identity with inequality of the
global domain bounds.

`EnrichedQuotients.lean` proves incompleteness of consistent represented
Boolean quotients directly from the internal representation section and an
explicit subobject identification at `S`. Its equivalent conclusion excludes
the bound copairing from being a regular epimorphism. There is no independent
external representation premise in these two new quotient results.

The remaining construction is the global total-arrow and predicate comparison,
including the natural identification along `J`. The fully packaged enriched
theorem and numerical/arithmetic interpretation are not claimed. See
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for the exact boundary.
The source toolchain and imported provenance are unchanged. The documented
hosted executable-path restriction occurred and its adapter was used;
Palomar Comparator, NanoDa, and con-ron were not run.

Evidence is retained in
[Audit/2026-10-28-enriched-restriction](Audit/2026-10-28-enriched-restriction/).

## Internal separator checkpoint

Verified on 2026-10-28 using Lean 4.35.0-rc2 on Linux x86-64, starting from
`94390c5b4f84125bd9b245d966ad1aed6b5dbd0e`. The existing checkout was clean,
and the remote `main` agreed before editing.

- `python3 scripts/verify.py`: PASS.
- Combined entry point: PASS (1896 jobs, including cached dependencies).
- Transitive axiom inspection: PASS for all 62 declarations, retaining every
  previous check. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
- All sixteen dependency revisions and all 356 imported-file records match
  their pins or the two pre-existing recorded patches.
- All four new modules compile without warnings. The two existing imported
  linter warnings remain.
- The scan of all fourteen project Lean files found no `sorry`, `admit`,
  `axiom`, or `opaque` declarations. No imported source was changed.

`InternalLattices.lean` constructs the actual complementary-pair pullback
and its universal projections and lifts. `InternalCartesian.lean` specifies
internal total-arrow operations and predicate actions, with their structural
equations at every parameter. `InternalDiagonal.lean` proves the diagonal
calculation at arbitrary parameters. `InternalRepresentation.lean` constructs
the representation pullback and derives generalized representatives from its
section. At the actual separator equalizer, it constructs `gamma`, composes
it with `rho`, and proves `Sep → Z_U` and the factorization equation. It also
proves the no-global-separator and strict-initial-object consequences.

Deriving this internal total-arrow structure from the enriched restriction
hom-objects remains open. The full enriched categorical theorem and the
numerical/arithmetic interpretation are not claimed. See
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) for the exact boundary.
The source toolchain and imported provenance are unchanged. The documented
hosted executable-path adapter was used; Palomar Comparator, NanoDa, and
con-ron were not run.

Evidence is retained in
[Audit/2026-10-28-internal-separator](Audit/2026-10-28-internal-separator/).

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
