# Monic partial-slice comparison and universal computations for v57

Proof commit `62aef20d5c22faa9f754bb3ee64218e3954f686a` identifies the actual monic partial-map
slice with ambient partial morphisms over T and constructs its fixed-input
restriction products and universal computations. **Lemma 5.1 remains open**:
arbitrary slice-object products, the constant-object recursion subcategory
and its splitting equivalence remain. There are still **67 proved numbered
counterparts and ten open obligations**.

## Constructions

`V46MonicSpanValues` proves partial-inverse uniqueness directly from the
restriction laws. Under the printed monic partial-inverse hypothesis it
classifies mono-left total spans by their values and proves pullback
composition. Splitting each morphism's domain gives a representing span.
`V46MonicPartialMapEquivalence.selfEquivalence` then proves
`Par(Tot C,Mono) ≌ C`. Neither result assumes ranges or weak choice.
The existing range-based comparison and span definitions are preserved.
The shared partial-cone lifting lemma now omits its two unused range and
weak-choice premises; its proof is unchanged.

`V46AmbientPartialSlice` constructs the category whose objects are total
families `p:X→T` and whose partial morphisms satisfy
`f ≫ q = rst f ≫ p`. It supplies restriction, totality and the
restriction-terminal family. `V46PartialSliceEquivalence` proves this
category equivalent to the actual `Par(Tot(C)/T,Mono)`, preserving
restriction in both directions and preserving and reflecting totality.
Fullness reconstructs a span over T; faithfulness lifts its apex
isomorphism back into the total over category.

`V46AmbientSliceTuring` and `V46PartialSliceTuring` construct products
with any fixed constant input family. They prove total projections,
partial pairing with its restriction/projection equations, reconstruction
from projections and the product universal property on total morphisms.
The tensor functor preserves restriction and is identified with the
canonical partial pairing construction in the ambient category.

The universal computation theorem quantifies over arbitrary morphisms
in the actual monic-span quotient. It produces a total parameter in the
same partial slice. The constant object is the literal family `T×Q→T`;
the evaluator's value is the associator followed by `1_T×τ`.

The product-derived and existing restriction structures on `Split(R)`
are proved equal. The statement checks transfer the existing splittings,
monic partial inverses and total pullbacks along that equality.

## Verification

All **24 incremental integration commands passed**, including seventeen
strict commands and 42 selected axiom reports. The project and both
statement entry points were rebuilt, including dependencies affected by
the generalized pullback helper. The strict commands cover all new files,
both changed producer files and selected existing dependency interfaces,
the project entry point, both statement audits and the current axiom audit.
The retained statement and axiom audits also passed.

The complete transitive audits cover **881 current production modules**,
**27,698 current declarations** and **1,274 retained declarations**.
Both axiom unions are exactly `propext`, `Quot.sound`, `Classical.choice`.
All sixteen dependency worktrees were clean and pinned at both ends, all
356 imported-source comparisons and all four retained manuscript-source
provenance comparisons passed. All 2,367 measured inputs match the tested
proof commit and were unchanged during verification.

The [machine-readable record](V57_PARTIAL_SLICE_VERIFICATION_2026-11-13.json)
contains the exact scope, commands, log hashes, baseline evidence and proof
status. Raw logs remain at `.codex-work/v57-span-comparison-20261113/incremental-verification`.

- Source snapshot SHA-256: `1f21e67cea1a6001bdb9fb84666cedc16936fa37d878c5327cf9fbdc4078a437`.
- Raw verification JSON SHA-256: `740ce40eee1777eeccb977d1e19cd78fc3136db6bad8bb31351bbfe84764be27`.

This is incremental verification. The full 1,708-command replay and all
earlier incremental evidence remain preserved. The active manuscript is
v57; its source, PDF, archive, manifest and instructions retain their
previous bytes. The unrelated Palomar workflow and declaration notes
were preserved.
