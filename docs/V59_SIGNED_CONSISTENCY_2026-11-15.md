# PA consistency and regular-image generation for Lemma 8.9

Seven producers and three independent Checks modules prove the PA
consistency sentence and the internal consistency equation for the generated
signed theory in the PA predicate category. The signed axiom morphism
presents the join of the two atomic images. Its canonical sentence image
agrees with generation from that regular-image axiom subobject for every
subobject-indexed choice of initial derivation algebras.

Lemma 8.9 remains open: the comparison with the printed restriction
splitting and the essential-incompleteness assembly remain. The count is
**70 of 77 numbered results proved**. Manuscript v59 is unchanged.

## Construction

`ArithmeticSignedTheoryTruth.consistencySentence` uses the actual canonical
proof carrier and chosen graphs of its conclusion and formula negation.
`consistency_PA` applies first-order completeness to the proved contradiction
exclusion in every PA model, including at nonstandard proof codes.

`PredicateModelSubobjects` proves that emptiness in every model gives a
provable inclusion into the empty predicate, an initial object and the
bottom subobject. The existing represented image corestriction supplies a
witness section for the categorical image factor. Consequently every point
of an interpreted image subobject has an actual source witness.
`PredicateImageConsistency.image_consistent` uses those witnesses on the
intersection of the proof image and its negation inverse image. The
all-model contradiction proves that intersection is bottom.

`formula_consistent` applies this construction to the diagonal proof
algebra. `sentence_consistent` restricts it to the actual sentence inclusion,
using the proved sentence-negation square and preserved bottom subobject.
These are categorical subobject equations, with the chosen images retained.

`ArithmeticSignedGeneration.proofFamily` is indexed only by axiom
subobjects. `presentation_image_comparison` compares the independently
constructed arithmetic proof codes for an arbitrary axiom morphism with
generation from its regular image. The image factor and its constructed
section induce the two rule comparisons. The existing copairing-image
result identifies the regular image of the signed axiom morphism with the
join of the positive and negative atomic images.

`generated_eq_canonical` proves independence from the initial-algebra
choice at each axiom subobject. `signed_theory_eq` identifies the resulting
`SignedFirstOrder.theory` with the canonical sentence image.
`signed_theory_consistent` proves its consistency for every supplied
`NullaryPresentations` in the PA predicate category, with no consistency
conclusion as a premise. `SyntacticDerivation.nullaryPresentations` also
constructs this presentation family from the existing plain parameterized
syntax and arithmetic derivation algebras. Independent checks instantiate
that construction and state the expanded PA sentence, formula and sentence
image equations, arbitrary-morphism regular-image comparison and generated
signed consistency equation.

## Verification

Proof commit: `3d48afb8750603111ec37b672b379dc344337f24`. All **22 incremental commands**
passed, including **14 strict elaborations**, the project build, both
statement audits, parser tests, manuscript gate and both complete transitive
axiom audits. The current audit covers **976 production modules**
and **29,445 declarations**; the retained audit covers
**1,274**. All **28 principal axiom reports** and both
complete audits use only `propext`, `Quot.sound` and `Classical.choice`.
All 16 dependency worktrees remained clean and pinned; 356 source-provenance
pins were checked. All **2,486 measured inputs** remained unchanged
and matched the proof commit.

The controlled delta from the prior incremental verification contains the
ten new Lean files, four production/audit entry points and the selected
correspondence table. Both the prior incremental and full v59 baseline
inputs were matched to their published proof commits before comparison.
The [machine-readable record](V59_SIGNED_CONSISTENCY_VERIFICATION_2026-11-15.json) records command logs and hashes,
principal axiom reports, module coverage and the baseline comparisons. The
raw record is `.codex-work/v59-consistency-20261115/incremental-verification/verification.json`,
SHA-256 `b04faab1bdd70b8941217fbe2523ab75562f9ac9eeb7fad220169ae2a93770c8`.

This is completed **incremental verification**, not a new full replay.
The last completed [full v59 replay](V59_FULL_VERIFICATION_2026-11-14.md)
remains the 1,798-command run at `8df18834734179186459d3c4c34d4c0cf20b6194`.

## Remaining assembly

Compare these predicate-category diagonal subobjects and their signed theory
with the same objects in `Split(S_PA)` and its total category. The existing
`SplitObject.inclusion_inseparable` applies to
`ArithmeticDiagonalCodes.source_pair_inseparable`; reuse this theorem for
arbitrary candidate separators in the splitting. Identify the alpha and
beta predicate idempotents with the actual source pair using the proved
all-model comparisons and program-class extensionality. Apply the proved
free signed-theory criterion with every consistent complete extension
quantified. Add independent checks of all printed clauses before changing
Lemma 8.9's numbered status. No new manuscript defect has been established.
