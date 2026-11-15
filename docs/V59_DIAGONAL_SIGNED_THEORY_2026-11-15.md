# Lemma 8.9: the arithmetic diagonal signed theory

Lemma 8.9 is complete through the constructed predicate-equivalence
realization in the total restriction splitting. The current count is
**71 of 77 numbered results proved**, with Corollary 8.10 next.
Manuscript v59, its source, PDF, archive and manifest are unchanged.

## Constructed comparison

`ArithmeticDiagonalSplitting.alpha_idem` and `beta_idem` identify the
actual arithmetic predicate idempotents with the manuscript's source
idempotents a0 and a1. The existing full inclusion theorem transfers their
inseparability to the restriction splitting, including every candidate
complementary separator there.

`ArithmeticSignedSeparator` extracts a c.e. standard set from every
predicate subobject. A complementary partition gives complementary c.e.
sets, hence a computable separator. The existing categorical diagonal
no-separator theorem excludes it. Together with the all-model disjointness
proof, this gives `ArithmeticSignedEssential.diagonal_inseparable`.
The proved free signed-theory criterion now gives consistency and
incompleteness of every consistent closed predicate extension.

`EquivalenceSubobjects` constructs the order isomorphism on all subobjects
of an equivalence, proves its regular-image and direct-image comparisons,
and transfers inseparability. `ArithmeticSignedTotal` uses the actual
predicate equivalence into `Tot(Split(S_PA))`. Its logical and sentence
morphisms are the transported ones; the quantifier and implication inputs
use the proved product comparisons. Its proof algebras are the actual coded
target derivation algebras, indexed only by axiom subobjects.

The signed axiom join is the join of the images of the two actual target
inclusions followed by the atom morphism and its negative. The constructed
closed-rule-algebra comparison bounds target generation by the mapped
consistent predicate theory. Preservation of meets, bottom and the
negation pullback proves consistency of the generated target theory.
The atomic bounds exclude a complete consistent extension for every closed
target sentence subobject. There is no restriction to extensions selected
from a particular presentation or constant family.

`ArithmeticSignedSplitGenerators` identifies the numerical carrier with
the included omega object and the underlying generator morphisms with a0
and a1. `ForwardSyntaxTransport` transports the actual two-sorted algebra,
its folds and initiality for every target parameter. `syntaxInitial`,
`syntaxStable` and `syntax_carrier` establish the free syntax underlying
the transported calculus. The no-function coefficient is initial by
preservation of the source initial object. This realization uses the
proved equivalence; it makes no assertion that a chosen inverse-equivalence
code chart fixes numerical words.

`ArithmeticSignedTheory.printed_statement` assembles the printed PA
consistency premise, full source inseparability, internal base consistency
and the quantifier over all closed consistent extensions. Its presentation
and proof family are constructed. `presentation_generation` generates an
arbitrary axiom morphism through its regular image. No preservation,
consistency or incompleteness conclusion is added as a hypothesis.
The Boolean conventions and the previously proved internal PA truth and
consistency results are retained.

Three independent Checks modules state the predicate and target conclusions,
expand the signed image join and inference presentation, check actual split
generators and free syntax, and state the complete printed conclusion with
all extension quantifiers. All eight producers and three Checks modules
passed the eleven targeted strict elaborations before the proof commit.

## Verification

Proof commit: `ec7b99a98cb8c2c45d12f96d7333b316a565a606`. All **23 incremental commands** passed,
including **15 strict elaborations**, the project build, both statement
audits, parser tests, manuscript gate and both complete transitive axiom
audits. The current audit covers **984 production modules**
and **29,607 declarations**. The retained audit covers
**1,274 declarations**. All **35 principal axiom reports**
and both complete audits use only `propext`, `Quot.sound` and
`Classical.choice`. All sixteen dependency worktrees remained clean and
pinned; 356 source-provenance pins were checked. All
**2,497 measured inputs** remained unchanged and matched the
proof commit.

The controlled delta from the previous incremental verification consists of
the eleven new Lean files, four production/audit entry points and the selected
correspondence table. Both the previous incremental and full v59 baseline
inputs were matched to their published proof commits before comparison.
The [machine-readable record](V59_DIAGONAL_SIGNED_THEORY_VERIFICATION_2026-11-15.json) contains command hashes, audit coverage,
principal reports and baseline comparisons. The raw record is
`.codex-work/v59-essential-20261115/incremental-verification/verification.json`,
SHA-256 `941b5c4760695b8683c2f45a9bac48d5841442bbac5ca54cf430bc22a87f8b47`.

This is completed **incremental verification**, not a new full replay.
The last completed [full v59 replay](V59_FULL_VERIFICATION_2026-11-14.md)
remains the 1,798-command run at `8df18834734179186459d3c4c34d4c0cf20b6194`.

## Next obligation

Corollary 8.10 requires the actual associated-category application of
Theorems 5.2–5.3, including arbitrary consistent internal extensions, the
parameterized deduction hypotheses, common logical theorem and Boolean
no-total-extension witness. The six remaining numbered obligations are
8.10, 9.6, 9.8, 10.7, 10.8 and 10.9. Keep review commentary outside the
manuscript and preserve the current artifacts and dependencies.
