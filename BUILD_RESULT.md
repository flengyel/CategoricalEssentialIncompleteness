# Categorical essential incompleteness: build result

## Numerical restriction products and comparisons checkpoint

Verified on 2026-10-29 using Lean 4.35.0-rc2, starting from
`7befddd873d85750721aafb2f47f913cda082ddf`. The checkout was clean and remote
`main` agreed before editing.

- `python3 scripts/verify.py`: PASS (1941 jobs, including cached dependencies).
- All 311 axiom audits pass, retaining the previous 273. Only `propext`,
  `Classical.choice`, and `Quot.sound` occur.
- The sixteen dependency revisions, 356 imported-file records, and both
  manuscript hashes match their recorded values. No imported source, pin,
  or manuscript file was changed.
- All five new modules compile without warnings. The two imported linter
  warnings remain. The 56 project Lean files contain no proof holes or new axioms.

Partial pairing is defined on the intersection of the component domains.
The restriction projection equations, reconstruction from projections, and
precomposition law are proved. Recursive tuple coding gives all `PCategory`
equations, including associator and symmetry naturality. Both zero-absorption
laws establish `Prodominical Numerical`.

The induced restriction and the original numerical restriction are proved
equal as structures. Explicit functors give an equivalence between their
total-arrow categories and identify their product pairings. Total pairing
also agrees with the existing numerical product lift and its PER image.
The numerical domain lattice is order isomorphic to `DomSemilattice`, with
the same underlying arrows. C.e. unions construct `DomainJoins Numerical`;
the bounded lattice comparison preserves partial inverse image.

The next construction is a recursive isomorphism between each infinite
recursive numerical carrier and `ℕ`, establishing isotype. The Turing
morphism, indexing, Set-enrichment, and arithmetic syntax/provability
comparisons remain open.

The hosted executable-path adapter was used; ordinary Debian/WSL2 builds do
not need it. Palomar Comparator, NanoDa, and con-ron were not run. Evidence:
[Audit/2026-10-29-numerical-restriction-products](Audit/2026-10-29-numerical-restriction-products/).

## Numerical Boolean arrows and complemented subobjects checkpoint

Verified on 2026-10-29 using Lean 4.35.0-rc2, starting from
`f51ca8e82ba08603f206f51f1ec1b37ad047e45d`. The checkout was clean and remote
`main` agreed before editing.

- `python3 scripts/verify.py`: PASS (1936 jobs, including cached dependencies).
- All 273 axiom audits pass, retaining the previous 247. Only `propext`,
  `Classical.choice`, and `Quot.sound` occur.
- The sixteen dependency revisions, 356 imported-file records, and both
  manuscript hashes match their recorded values. No imported source, pin,
  or manuscript file was changed.
- All five new modules compile without warnings. The two imported linter
  warnings remain. The 51 project Lean files contain no proof holes or new axioms.

The explicit Boolean PER is a coproduct of terminal PERs, with a proved
isomorphism to the chosen object `1 + 1` and equations for both points.
Arrows from `D_ℕ` to this PER correspond bijectively to total recursive
Boolean functions. Their fibers are the recursive inverse-image support
inclusions, and every recursive subset occurs as an upper fiber.

The complemented subobjects of `D_ℕ` are exactly these recursive support
inclusions, equivalently the images of complementary numerical domain pairs.
The domain embedding also reflects existence of a complement on `ℕ`.
Together with the preceding constructions, these results complete
`lem:integration-numerical-subobjects`.

The next construction is numerical restriction products, including partial
pairing and the restriction projection equations. Recursion/indexing,
Set-enrichment, and arithmetic syntax/provability comparisons remain open.

The hosted executable-path adapter was used; ordinary Debian/WSL2 builds do
not need it. Palomar Comparator, NanoDa, and con-ron were not run. Evidence:
[Audit/2026-10-29-numerical-boolean](Audit/2026-10-29-numerical-boolean/).

## Numerical predicate and domain-embedding checkpoint

Verified on 2026-10-29 using Lean 4.35.0-rc2, starting from
`43ef82666d9919cdea35f1a59bd0557f450a6830`. The checkout was clean and remote
`main` agreed before editing.

- `python3 scripts/verify.py`: PASS (1931 jobs, including cached dependencies).
- All 247 axiom audits pass, retaining the previous 213. Only `propext`,
  `Classical.choice`, and `Quot.sound` occur.
- The sixteen dependency revisions, 356 imported-file records, and both
  manuscript hashes match their recorded values. No imported source, pin,
  or manuscript file was changed.
- All five new modules compile without warnings. The two imported linter
  warnings remain. The 46 project Lean files contain no proof holes or new axioms.

The checkpoint constructs the numerical domain and full PER subobject
predicate functors and their injective natural bounded lattice embedding.
Restriction inverse image preserves bottom, meets, and joins for partial
arrows, and top for total arrows. The domain embedding preserves the bounded
lattice operations and preserves and reflects complementarity of a specified
pair. The general subobject predicate construction derives distributivity
and bounded lattice reindexing from regularity and finite extensivity.

The next construction is the Boolean-fiber and complemented-subobject
characterization in `lem:integration-numerical-subobjects`. Numerical
restriction products, recursion/indexing, Set-enrichment, and arithmetic
syntax/provability comparisons remain open.

The hosted executable-path adapter was used; ordinary Debian/WSL2 builds do
not need it. Palomar Comparator, NanoDa, and con-ron were not run. Evidence:
[Audit/2026-10-29-numerical-predicates](Audit/2026-10-29-numerical-predicates/).

## PER coproducts and extensivity checkpoint

Verified on 2026-10-28 using Lean 4.35.0-rc2, starting from
`9d9f2e4d1be9c83a74c155377053917cc40e703f`. The checkout was clean and remote
`main` agreed before editing.

- `python3 scripts/verify.py`: PASS (1926 jobs, including cached dependencies).
- All 213 axiom audits pass, retaining the previous 191. Only `propext`,
  `Classical.choice`, and `Quot.sound` occur.
- The sixteen dependency revisions, 356 imported-file records, and both
  manuscript hashes match their recorded values. No imported source or pin
  was changed.
- All four new modules compile without warnings. The two imported linter
  warnings remain. The 41 project Lean files contain no proof holes or new axioms.

The checkpoint constructs finite PER coproducts, proves monicity of their
injections, and proves that the copairing of the two inverse images of the
summands is an isomorphism. The injection squares into the coproduct of terminal
objects are pullbacks. These results give the van Kampen property,
`NumericalPER.perFinitaryExtensive`, and disjointness of the injections.
Together with the preceding regularity proof, this supplies the regular
extensive target required by the numerical interpretation.

The next construction is the numerical domain embedding as a natural bounded
lattice homomorphism. Numerical restriction products, recursion/indexing, and
the arithmetic syntax/provability comparison remain open.

The hosted executable-path adapter was used; ordinary Debian/WSL2 builds do
not need it. Palomar Comparator, NanoDa, and con-ron were not run. Evidence:
[Audit/2026-10-28-per-extensive](Audit/2026-10-28-per-extensive/).

## PER regularity checkpoint

Verified on 2026-10-28 using Lean 4.35.0-rc2, starting from
`994323256483136cfd23c3e935a826d18aa6b9cf`. The checkout was clean and remote
`main` agreed before editing.

- `python3 scripts/verify.py`: PASS (1922 jobs, including cached dependencies).
- All 191 axiom audits pass, retaining the previous 179. Only `propext`,
  `Classical.choice`, and `Quot.sound` occur.
- Sixteen dependency revisions, 356 imported-file records, and both manuscript
  hashes match their recorded values. No imported source or pin was changed.
- Both new modules compile without warnings. The two imported linter warnings
  remain. The 37 project Lean files contain no proof holes or new axioms.

`PERPullbacks` constructs pullbacks of arbitrary PER morphisms.
`NumericalPER.pullbackSnd_regularEpi` proves stability of regular epimorphisms;
`NumericalPER.perRegular` combines this with finite limits and kernel-pair
coequalizers to give a regular category. The proof extracts a representing
partial recursive function from the inverse of the image inclusion. It assumes
no enumerability of PER supports or relations.

The next construction is PER binary coproducts and their pullback stability,
followed by extensivity. Numerical restriction products, recursion/indexing,
and arithmetic syntax/provability comparisons remain open.

The hosted executable-path adapter was used; ordinary Debian/WSL2 builds do
not need it. Palomar Comparator, NanoDa, and con-ron were not run. Evidence:
[Audit/2026-10-28-per-regular](Audit/2026-10-28-per-regular/).

## Numerical limits, regular images, and terminology revision

Verified on 2026-10-28 using Lean 4.35.0-rc2 on Linux x86-64, starting from
`69100418d5d8dd8c77a2b98a06939593aecdc51a`. The original checkout and remote
`main` agreed. Subsequent work was preserved.

- `python3 scripts/verify.py`: PASS (1920 build jobs, including cached dependencies).
- Transitive axiom inspection: PASS for 179 declarations. All 152 previous
  checks are retained, with two names updated from `Tracker` to `Representative`.
  Only `propext`, `Classical.choice`, and `Quot.sound` occur.
- The sixteen dependency revisions and 356 imported-file records match their
  pins or recorded patches. Toolchain and dependency pins are unchanged.
- Thirteen imported files have comment-only revisions, checked against their
  original noncomment source. Original and revised hashes are recorded.
- The scan of all 35 project Lean files found no `sorry`, `admit`, `axiom`, or
  `opaque` declarations.
- The revised manuscript and rebuilt 33-page PDF have verified provenance
  hashes. The final LaTeX pass reports no warnings or overfull/underfull boxes. All 64 labels
  and 19 bibliography keys are unchanged.

The mathematical additions construct binary products of numerical total arrows
and their preservation by `J`, finite limits in the arbitrary-PER category,
regular-epimorphism/monomorphism factorizations, and coequalizers of kernel pairs.
Pullback stability of regular epimorphisms is the next unresolved lemma.
Extensivity, numerical restriction products and recursion, and the arithmetic
syntax/provability comparison remain open.

Terminology revisions replace `Tracker` with `Representative`, rename
`InternalBridge` to `ParameterizedEqualizer`, and remove informal assessments,
redundant assurances, vague descriptions, and stale references. Definitions,
mathematical hypotheses, and numeralwise/uniform provability distinctions are
retained. The separate editorial report records the reviewed scope and the
unavailable governing-source limitation.

The hosted executable-path adapter was used. Ordinary Debian/WSL2 builds do
not need it. Palomar Comparator, NanoDa, and con-ron were not run. Evidence:
[Audit/2026-10-28-per-limits](Audit/2026-10-28-per-limits/).

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
arbitrary-PER category uses arrows defined by equivalence classes of representing functions, and the functor from
total numerical arrows to equality PERs is proved full and faithful.

Support inclusions are categorical subobjects. Their order and
equality reflect support inclusion and equality. The inverse-image square
satisfies the full pullback universal property and agrees with restriction
inverse image. Dovetailing proves that c.e. support unions are least upper
bounds among all categorical subobjects. For disjoint supports, absence of a
complementary-domain separator is equivalent to recursive inseparability.

This establishes the support comparison in part (ii) of
`thm:integration-essential-equivalence`. The next construction is numerical
binary products and their preservation by `J`. Remaining PER regular/extensive
structure, the bounded lattice homomorphism structure, and the syntax/provability and
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

The natural predicate identification along `J` gives a natural
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
including the natural identification along `J`. The enriched
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
subobject fibers. See [the precise correspondence and remaining
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
