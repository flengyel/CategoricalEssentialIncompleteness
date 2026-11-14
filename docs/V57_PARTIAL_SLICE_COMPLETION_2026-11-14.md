# Lemma 5.1: partial-slice Turing theorem completed

Proof commit `d2acc5c940c75a8e8fd2e976db63453ed675cb4a` completes manuscript v57 Lemma 5.1.
The literal full subcategory R[T] of original constant families is a
recursion category, and its restriction splitting is equivalent to the
actual monic partial-map slice C[T]. Together with the earlier Turing
structure of Split(R) and C[T], this raises the count to **68 proved
numbered counterparts and nine open obligations**. The first open result
is Theorem 5.2.

## Constructions

`V46RestrictionCompletion` proves a general completion theorem for a full
faithful restriction functor F:A→B. Chosen splittings of the images of
restriction idempotents define a functor Split(A)→B. Its morphism action
is m_e≫F(f)≫r_d. Fullness and faithfulness are proved directly. If each
B object has a total embedding and partial retraction into an F image,
with s≫j=rst(s), the extension is essentially surjective. The resulting
equivalence preserves restriction in both directions. The hypotheses
use splitting and total retractions, without range or coproduct premises.

`V46FullRestrictionProducts` transfers binary restriction products to a
full restriction subcategory closed under products up to specified
isomorphism. It proves comparison naturality and transfers a universal
Turing morphism with total parameters. `V46ConstantFamilyProducts`
constructs the constant-family functor, the associator isomorphism and
the canonical comparison with arbitrary slice products.

`V46RestrictionProductZeros` derives the two prodominical absorption laws
from restriction products and restriction zeros. `V46AmbientProductTuring`
proves the Turing property for the complete ambient slice product
structure. `V46PartialSliceRealization` proves that the literal-family
realization in the actual span quotient is full, faithful and preserves
restriction.

`V46ConstantSlice` and `V46ConstantSliceRecursion` give the indexed
presentation on original objects of R, its chosen product structure,
isotype, zeros, Turing morphism and completion. `V46ConstantSliceFull`
constructs the literal full subcategory on families T×X→T, with X an
original R object. The chosen products remain in this subcategory;
their derived restriction agrees with its inherited restriction.
Original isomorphisms give isotype, inherited zeros satisfy absorption,
and the universal evaluator gives an actual `PRecursionCategory`.

The full faithful realization has exactly the stated constant objects
as its object range. Every ambient slice family is a total retract of
one of these objects. Applying the completion theorem and the proved
monic-span equivalence constructs Split(R[T])≃Par(D/T,Mono), preserving
restriction in both directions.

`V46PartialSliceTuringTheoremChecks` checks all clauses of the printed
lemma: the universal object in Split(R), restriction terminal morphisms,
the actual slice Turing morphism and total retractions, the literal
full recursion subcategory, its exact object range and its splitting
equivalence. The earlier evaluator-value theorem identifies the slice
computation with the associator followed by 1_T×τ. The proof uses the
printed monic partial-inverse hypothesis and total pullbacks; the
printed regularity supplies the needed total limits.

## Verification

All **25 incremental commands passed**, including **18 strict commands**.
The selected axiom checks contain **106 reports**, including **39 in the
complete Lemma 5.1 checks**.
The project and both statement entry points were rebuilt. Strict checks
cover all nine new producers, the assembled theorem checks, four selected
existing interfaces/check modules, the root, both statement audits and
the current axiom audit. Both retained audits also passed.

The complete transitive audits cover **899 current production modules**,
**28,078 current declarations** and **1,274 retained declarations**.
Both axiom unions are exactly `propext`, `Quot.sound`, `Classical.choice`.
All sixteen dependency worktrees were clean and pinned at both ends;
all 356 imported-source and four retained manuscript provenance
comparisons passed. All 2,387 measured inputs match the tested proof
commit and were unchanged during
verification. The drift check found no change in the
2,377 previous inputs before this work.

The [machine-readable record](V57_PARTIAL_SLICE_COMPLETION_VERIFICATION_2026-11-14.json) contains the commands,
log hashes, source snapshot, baseline evidence and proof status. Raw
logs remain at `.codex-work/v57-constant-slice-20261114/incremental-verification`.

- Source snapshot SHA-256: `2bff2e5ae27322d3cea08a16644d2432377d8db9faa970a27c2f07c99998cb56`.
- Raw verification JSON SHA-256: `6127c2d8c40a5449ab06a0d0dd2bd8a59b8f14e833cd8920a5c5a58eceae8678`.

This is incremental verification. The earlier full 1,708-command replay
and all earlier incremental evidence remain preserved. The active
manuscript remains v57; source, PDF, source archive, manifest and current
instructions retain their previous bytes. The unrelated Palomar workflow
and declaration notes were preserved.
