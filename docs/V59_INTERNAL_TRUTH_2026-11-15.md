# Internal truth and common-support contradiction for Lemma 8.9

Eight producers and three independent Checks modules prove the truth
invariant on the actual diagonal signed derivation algebra in every PA
model. Both proposed contradictory derivations use the same constructed
combined alpha-support. Their conclusions cannot be a formula and its
negation, including when the derivation codes and support lengths are
nonstandard. Lemma 8.9 remains open pending the generated-theory consistency
and essential-incompleteness assembly. The count is **70 of 77 numbered
results proved**. Manuscript v59 is unchanged.

## Construction

`ArithmeticFiniteCoverage.Covers(s,l)` says that every entry of s occurs in l.
The constructed Sigma-one and Pi-one definitions apply at arbitrary internal
lengths. The proved append equation splits coverage into the two children's
coverage. `CoveredDerivationInvariant.formula` places Sigma-one graph and
coverage formulas in antecedents, producing a Pi-one formula whose exact
semantics is the truth invariant at a fixed support. The existing PA
internal rule induction applies to this coded predicate.

`SignedDerivationTruthGeometry` proves the actual ordered-child, conclusion
and support coordinates of the original canonical signed proof algebra.
Generalization retains its child's support. Modus ponens concatenates the
two ordered supports. The nullary matching pullback adds no data to a rule
label. `ParameterizedBooleanModelTruth` proves both inference steps at
individual model inputs; their truth premises need not hold elsewhere in
the input object. `SignedDerivation.truth_from_leaves` then proves internal
soundness by the coded Pi-one induction, using the actual typed constructors.

`ArithmeticSignedAtoms` constructs numerical inclusions of the actual alpha
and beta predicates into the printed number object, retaining their literal
codes. The finite-support valuation makes covered alpha-atoms true. PA
proves the disjointness that makes beta-negated atoms true on every
alpha-support. `ArithmeticSignedTheoryTruth.leaf_truth` discharges all three
leaf branches, including all seven logical schemes. `internal_truth` has
no leaf-soundness or consistency hypothesis.

`jointSupport` concatenates the two canonical positive supports as one
internal list of numbers. Its entries satisfy alpha, and it covers each
derivation's positive leaves. `joint_left_truth` and `joint_right_truth`
use that same support. Boolean negation and the disjointness of the two
actual coproduct injections prove `no_contradictory_derivations` in every
PA model. No preservation of initial algebras by model interpretation is
assumed. The independent checks instantiate the constructed plain PA syntax,
its actual signed rules, valuation and support without a syntax-existence,
truth or consistency premise.

## Verification

Proof commit: `071fcd77c9b41aeab3c1c5a9aa94fe8590daef2a`. All **23 incremental commands**
passed, including **15 strict elaborations**, the project build, both
statement audits, parser tests, manuscript gate and both complete transitive
axiom audits. The current audit covers **969 production modules**
and **29,368 declarations**; the retained audit covers
**1,274**. All **49 principal axiom reports** and both
complete audits use only `propext`, `Quot.sound` and `Classical.choice`.
All 16 dependency worktrees remained clean and pinned, and 356 source pins
were checked. All **2,476 measured inputs** remained unchanged and
matched the proof commit.

The controlled delta from the prior incremental run consists of the eleven
new Lean files, four production/audit entry points and the active
correspondence table. Both the previous incremental baseline and the full
v59 baseline were matched to their published proof commits before comparing
inputs. The [machine-readable record](V59_INTERNAL_TRUTH_VERIFICATION_2026-11-15.json) records command logs and hashes,
coverage, principal axiom reports and the baseline comparisons. The raw
record is `.codex-work/v59-internal-truth-20261115/incremental-verification/verification.json`,
SHA-256 `10c9f41b7d2f2ecaf2e2c7a0837468019c8b5c6cd313a0667d1063e4a88ac45e`.

This is completed **incremental verification**, not a new full replay.
The last completed [full v59 replay](V59_FULL_VERIFICATION_2026-11-14.md)
remains the 1,798-command run at `8df18834734179186459d3c4c34d4c0cf20b6194`.

## Remaining proof

Convert the all-model contradiction to the PA theorem and the actual
sentence-image consistency equation. Identify the printed generated signed
theory through the regular image of the axiom morphism, keeping initiality
indexed only by axiom subobjects. Transfer the actual diagonal source
inseparability to the required restriction splitting and apply the existing
free-theory essential-incompleteness criterion. Retain every extension
quantifier and add independent checks of the complete printed lemma before
changing its numbered status.
