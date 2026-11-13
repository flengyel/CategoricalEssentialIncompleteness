# Split Turing structure and slice equations for v57

Proof commit `7f361377d4f57b400c672fb30f495d85057dbdc0` proves the split-category product and
Turing constructions and the ambient slice parameter and retraction
equations used in Lemma 5.1. **The complete lemma remains open**: the
constructions still need to be realized in `Par(D/T)`, followed by the
constant-object recursion subcategory and its splitting equivalence. The
count remains **67 proved numbered counterparts and ten open obligations**.

## Proved constructions

`V46SplitProductCategory` packages all fourteen `PCategory` laws for the
chosen products of arbitrary split objects. It also proves both
prodominical zero-absorption laws. The structures are explicit; their
restriction operation agrees with the existing split restriction.

`V46SplitTuring.evaluator_isTuring` extends a base Turing morphism to
arbitrary split inputs, outputs and parameter objects. The code morphism
is total relative to the split source domain. `turing_object` constructs
a universal object and evaluator and proves that every split object embeds
totally into it with a partial retraction.

`V46RestrictionTerminal` derives the restriction-terminal law from a
terminal object of the total category and splitting restriction
idempotents. It proves totality, identity, uniqueness on total morphisms
and naturality for arbitrary partial morphisms.

`V46SliceTuringParameters.slice_parameterization` constructs the total
parameter `⟨p,a⟩` over `T` and proves the computation equation for
`1_T×τ`, including the associator. Its premise is the ambient partial
slice equation `φ ≫ p₀ = rst φ ≫ (p₀ ≫ p)`. The theorem
`total_retract_over` constructs the total graph embedding `⟨p,m⟩` and,
under the printed monic partial-inverse hypothesis, a partial inverse
satisfying the same equation over `T` on its domain of definition.

These are equations in the ambient restriction category. Their
identification with the monic spans of `Par(D/T)` remains part of the open
result. The whole partial slice is not asserted to be isotype.

## Verification

All **21 incremental integration commands passed**, including fourteen
strict commands. These rechecked the eight new source/check files, the
earlier split-products pair, the project entry point, both statement audits
and the complete current axiom audit. The project and both statement entry
points were rebuilt; the retained statement and axiom audits also passed.
All 28 selected axiom reports passed, including eighteen new reports.

The complete transitive audits cover **875 current production modules**,
**27,506 current declarations** and **1,274 retained declarations**.
Both axiom unions are exactly `propext`, `Quot.sound`, `Classical.choice`.
All sixteen dependency worktrees were clean and pinned at both ends of the
run, all 356 imported-source comparisons passed, and the four retained
manuscript-source provenance comparisons passed. All 2,360 measured inputs
match the tested proof commit and were unchanged during verification.

The [machine-readable record](V57_SPLIT_TURING_VERIFICATION_2026-11-13.json)
contains command and log hashes, scope, baselines and proof status. Raw
logs remain at `.codex-work/v57-split-products-20261113/incremental-verification`.

- Source snapshot SHA-256: `93854acf291810b95951f81c2c42a95a9440a761c50e58673e45525d4aed50a1`.
- Raw verification JSON SHA-256: `59da18f52274a89f22e2209e43d761431bdaabbc8b8820721848dce76a7a5b8d`.

This is an incremental verification. The preceding 17-command prerequisite
run and the full 1,708-command replay remain preserved. The new batch has
fourteen measured changes: eight added Lean files, four import entry
points, the correspondence table and a documentation correction in the
earlier split-products module. No earlier proof body changed.

The active manuscript remains v57. Its source, PDF, archive, manifest and
instructions retain their previous bytes. The unrelated Palomar workflow
and declaration notes were preserved.
