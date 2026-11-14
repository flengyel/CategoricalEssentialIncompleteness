# Manuscript v58: closure-transfer integration and verification

Proof commit `21821a893cf054d78696041eadc15a76124a2cd5` integrates the constructed closed-theory
transport with manuscript v58. The concurrent manuscript and reviews from
`df66b19853e6b243170725619bfabb71f4741065` were merged without discarding local
proof work. The active manifest, PDF, source archive, correspondence and
instructions select v58. The count remains **69 proved numbered counterparts
and eight open obligations**; Theorem 5.3 remains open.

## Revision correspondence

A whitespace-normalized comparison of all **77 numbered results and three definitions**
found no statement or definition change between the retained v57 source and
v58. The source comparison and normalized statement hashes are included in
the [machine-readable record](V58_CLOSED_THEORY_TRANSFER_VERIFICATION_2026-11-14.json). The authored v58 source, PDFs,
archive and manifest retain their incoming bytes. Later remote impact-review
and continuation instructions were merged separately; these documentation
changes do not touch the measured proof or manuscript inputs.

The revision makes the Boolean quantifier operation explicit as π₂, aligns
Appendix B's equality convention with the true/second injection, clarifies
the abstract's associated-category equivalence, corrects the Bernardi
pinpoint, removes two repeated summaries and expands the uniform composition
argument in Lemma 6.1. `V46V58ConventionChecks` checks the second-projection
valuation, equality interpreted by true, true as the second injection,
internal equality's diagonal pullback along that injection, the fork equality
obstruction, the ordered two-stage trace model and the uniform PA composition
statement. These checks confirm the existing Lean conventions at explicit
types. No proof status is inferred from the prose changes.

The preserved [v57 closure-transfer snapshot](V57_CLOSED_THEORY_TRANSFER_2026-11-14.md)
records the earlier 24-command run on its frozen inputs. This report records
a fresh run on the merged v58 inputs.

## Constructed closure transfer

`V46FiniteRuleTransport` constructs the natural finite ordered premise tuple
comparison and the isomorphism of each typed rule pullback under a functor G
preserving finite limits. Projection and conclusion equations are proved.
`V46MappedRuleAlgebras` uses the inverse comparison to construct an actual
algebra on the mapped closed formula object, component by component.

`V46FirstOrderRuleTransport` constructs the nullary, unary and binary
rule-instance morphisms. The nullary morphism retains the logical and axiom
labels, including the canonical representative of the image axiom subobject.
The product comparisons retain the two ordered modus-ponens premises and
the quantifier conclusion. Closure is a proved conclusion of the resulting
rule-algebra construction.

`V46FiniteLimitSubobjects` proves monotonicity and pullback compatibility of
the mapped subobject. `V46ClosedTheoryTransfer.generation_le_image` folds the
target initial derivation algebra for the image axioms into the mapped closed
source formula algebra. Images and the sentence pullback give
Gen(image A)≤image(Gen A). Extensivity gives equality for closed A.
`closed_image` and `theoryFunctor` construct the corresponding images and
actual functor on closed sentence theories. Initiality is required only for
axiom subobjects in the indicated calculi.

`V46RegularSlices` derives regularity and finite extensivity of ordinary
slices from the base hypotheses. `V46SliceBaseChangeGeometry` constructs the
ordinary constant-family right adjunction and proves finite-limit
preservation of that functor and terminal-point evaluation.
`V46SliceClosedTheories.constant_closed` and `evaluation_closed` instantiate
the closure construction for their literal mapped rule operations and provide
functors on the corresponding closed-theory categories.

Theorem 5.3 still needs the identification of the composed mapped calculus
with the original through the evaluation retraction, consistency/completeness
preservation and the full essential-incompleteness equivalence. The earlier
actual partial-slice retraction and Boolean-morphism equivalences are retained.

## Verification

All **26 fresh v58 incremental commands passed**, including
**18 strict commands**. The standalone current-manuscript
gate, axiom-parser tests, project build and both statement entry points passed.
Strict checks cover all eight closure-transfer producers, their assembled
checks, the v58 convention checks, four existing interfaces/check modules,
the root, both statement audits and the current axiom audit. Both retained
audits also passed.

Selected checks contain **157 axiom reports**,
including **27 in the closure checks**.
The complete current audit covers **927
production modules and 28,492 declarations**; the
retained audit covers **1,274 declarations**.
Both axiom unions are exactly `propext`, `Quot.sound`, `Classical.choice`.
All sixteen dependency worktrees were clean and pinned at both ends. All
356 imported-source and
4 retained manuscript provenance
comparisons passed. All **2,419 measured inputs** match
the tested proof commit and stayed unchanged during verification.

The measured delta is the audited upstream manuscript revision plus the new
convention checks, statement imports and active correspondence update. Old v57
artifacts and evidence remain preserved; the manifest selects v58 exclusively.

The [verification record](V58_CLOSED_THEORY_TRANSFER_VERIFICATION_2026-11-14.json) contains commands, log hashes, source
snapshot, upstream statement comparison and proof status. Raw logs remain at
`.codex-work/v58-closed-theory-transfer-20261114/incremental-verification`.

- Source snapshot SHA-256: `f6eecf0a6eb0bfae02e45a66de62b25bc46c4caf3354771501643552d3f79590`.
- Raw verification JSON SHA-256: `21ea1115011a6a0257631becffd3affbf91c2e762deaaf194d6e4cbe71e3e798`.

This is incremental verification. Earlier full and incremental evidence is
preserved; unchanged production files were not all individually re-elaborated.
The unrelated Palomar workflow and declaration notes were preserved.
