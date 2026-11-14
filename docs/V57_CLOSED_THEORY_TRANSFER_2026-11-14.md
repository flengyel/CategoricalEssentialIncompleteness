# Constructed closed sentence theory transport

Proof commit `c29d3a4f6a3f2d94972ff87eca2285c94946341c` constructs closure preservation from finite
rule diagrams and target derivation initiality. It also instantiates the
construction for constant families and evaluation in ordinary slices.
This run selected manuscript v57; its numbered-result
status remains **69 proved counterparts and eight open obligations**.

This report preserves the v57 snapshot used by this run. Revision v58 arrived
concurrently at `df66b19853e6b243170725619bfabb71f4741065`. Its 77 result and
three definition environments were compared and found identical. The separate
v58 closure-transfer report records integration and verification against the
revised current target. No numbered result is closed by this supporting batch.

## Constructions

`V46FiniteRuleTransport` constructs the natural comparison for finite ordered
premise tuples under a finite-limit-preserving functor G. It then constructs
an isomorphism between the mapped source pullback of each typed rule and its
target rule object, with both projection equations and the conclusion square.

`V46MappedRuleAlgebras` uses the inverse comparison to evaluate each target
rule component with the source algebra. Coproduct descent constructs an
actual algebra on the mapped conclusion object. A proved rule-instance
morphism can change the labels while preserving ordered premises and
conclusions. The closure construction needs finite-limit preservation;
the nullary instance morphism uses coproduct injections.

`V46FirstOrderRuleTransport` constructs these instance morphisms for the
nullary, unary and binary first-order rules. Nullary instances retain the
logical and nonlogical axiom labels; unary and binary instances use the
inverse product comparison. The binary premise equation retains both
ordered premises of modus ponens. The target axiom representative is carried
to the mapped source axiom by its actual underlying isomorphism.

`V46FiniteLimitSubobjects` constructs the mapped subobject, proves monotonicity
and its compatibility with ordinary pullback, and compares canonical
subobject representatives.

`V46ClosedTheoryTransfer.generation_le_image` transports the algebra on the
closed formula image of the source derivations. The target initial derivation
algebra for the image axioms folds into this mapped formula algebra. Taking
images and pulling back along the sentence inclusion proves
Gen(image A)≤image(Gen A). For closed A, extensivity gives equality.
`closed_image` and `theoryFunctor` therefore construct actual images of closed
sentence theories and their inclusion morphisms. The proof uses supplied
source and target initial derivations only for axiom subobjects; it constructs
the closure proof from the finite rule diagrams.

`V46RegularSlices` proves that regular epimorphisms in a slice are exactly
those with regular-epimorphic underlying morphisms. Kernel-pair coequalizers
and stable base change construct regularity of the slice. Preservation and
reflection by the forgetful functor also give finite extensivity of the slice.
These properties are derived from the base category hypotheses.

`V46SliceBaseChangeGeometry` constructs the ordinary right adjunction of the
literal constant-family functor to the forgetful functor. This proves its
finite-limit preservation. Pullback at a point from a terminal object,
followed by the terminal-slice equivalence, gives finite-limit-preserving
evaluation. `V46SliceClosedTheories.constant_closed` and `evaluation_closed`
instantiate the constructed closure theorem for their literal mapped rule
operations and supply functors on the corresponding closed-theory categories.

`V46ClosedTheoryTransferChecks` checks the general bound, closure theorem and
theory functor, the derived slice structures and finite geometry, and both
ordinary-slice closure instances at explicit types.

## Remaining correspondence work

Theorem 5.3 remains open. The composed mapped calculus still needs to be
identified with the original calculus through the evaluation retraction.
Consistency and completeness preservation and the full essential-
incompleteness equivalence then remain to be assembled. The v58 synchronization and its fresh current-input verification are
recorded separately. This report establishes only the retained v57 snapshot.

## Verification

All **24 incremental commands passed**, including
**17 strict commands** and both complete transitive
axiom audits. Selected checks contain **152
reports**, including **27 in the new
closure-transport checks**. The project and both statement entry points were
rebuilt. Strict checks cover all eight new producers, their assembled checks,
four selected existing interfaces/check modules, the root, both statement
entry points and the current axiom audit. Both retained audits passed.

The current audit covers **927 production
modules and 28,492 declarations**. The retained
audit covers **1,274 declarations**. Both axiom
unions are exactly `propext`, `Quot.sound`, `Classical.choice`. All sixteen
dependency worktrees were clean and pinned at both ends. All
356 imported-source and
4 retained manuscript provenance
comparisons passed. All 2,418 measured inputs match
the tested proof commit and stayed unchanged during verification. The drift
check found no change in the 2,409 previous
inputs before this work.

The [machine-readable record](V57_CLOSED_THEORY_TRANSFER_VERIFICATION_2026-11-14.json) contains command details, log
hashes, source snapshot and the unchanged numbered-result status. Raw logs
remain at `.codex-work/v57-closed-theory-transfer-20261114/incremental-verification`.

- Source snapshot SHA-256: `910734167eb2eec7d606dabd69735e94f7a9b5593bf5dd1fa846e31522b37540`.
- Raw verification JSON SHA-256: `89b43cd578d2e3109305ae75eb0a2e76c5a1abd2f6f3455583b74bfac6f55f7f`.

This is incremental verification; earlier full and incremental evidence
remain preserved. The current v57 source, PDF, source archive, manifest and
instructions retain their bytes. The unrelated Palomar files were preserved.
