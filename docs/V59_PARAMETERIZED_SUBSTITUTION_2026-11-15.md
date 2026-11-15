# Parameterized substitution and logical soundness for Lemma 8.9

Ten producers and three independent Checks modules prove Boolean valuation
invariance under admissible substitution while retaining arbitrary support,
binder and replacement parameters. The full Option equation also preserves
substitution failure. All seven logical schemes now have their parameterized
valuation laws, together with the previously proved two inference rules.
Lemma 8.9 remains open; the count is **70 of 77 numbered results proved**.
Theorem 5.3 remains complete. Manuscript v59 is unchanged.

## Construction

`ParameterizedOption` constructs evaluation on optional values with an
independent parameter and proves its constructor, naturality and mask laws.
`ConstantParameterAlgebra` reindexes the actual substitution algebra on
specified constant carrier families. Its comparison theorem identifies the
initial fold of this constructed algebra with the existing cross-parameter
fold. It uses the supplied parameterized initiality; it does not assume that
an arbitrary change of parameter preserves initial algebras.

`ParameterizedSubstitution.formula_value` identifies the formula component
of that fold with the original substitution fold, including its Option
result. The Boolean invariant compares this result with the original
formula's value, masked by the original success or failure. The five
constructor steps include both equal-binder and capture branches of
quantification. `AlgebraInvariant.fold_equalizes` then proves the invariant
for the constructed initial fold.

`ParameterizedBooleanValuation.substitution_option_value` holds for
arbitrary morphisms p : W → P, q : W → Q and f : W → F, where P is the
valuation parameter and Q is the actual substitution-parameter object.
`substitution_value` restricts to the actual admissible-substitution
subobject. Thus supports may vary independently of binders, replacement
terms and input formulas. No substitution-invariance conclusion is assumed.

The instantiation and equality-substitution laws use this constructed
invariance theorem. `logical_axioms_value` combines all seven schemes on
the actual logical-parameter coproduct, retaining arbitrary p : W → P.
True remains the second injection and quantification the second projection.
The independent checks state the full value equations and instantiate the
constructed finite-support atom assignment in the PA predicate category.
All producers and Checks modules are included in the production and audit
entry points. No manuscript statement or mathematical hypothesis is changed.

## Verification

Proof commit: `8a5f0cd7ee6d2ddd8b4f0619e20f7b35b8b08463`. All **25 incremental commands**
passed, including **17 strict elaborations**, the project build, both
statement audits, parser tests, manuscript gate and both complete transitive
axiom audits. The current audit covers **961 production modules** and
**29,208 declarations**; the retained audit covers **1,274**. All **61 principal
axiom reports** and both complete audits use only `propext`, `Quot.sound`
and `Classical.choice`. All 16 dependency worktrees remained clean and
pinned, and 356 source-provenance pins were checked.

All **2,465 measured inputs** remained unchanged and matched the proof
commit. The controlled delta from the previous incremental verification
contains the thirteen new Lean files, four production/audit entry points
and the active correspondence table. Both the prior incremental and full
v59 baseline inputs were matched to their published proof commits before
comparison.

The [machine-readable record](V59_PARAMETERIZED_SUBSTITUTION_VERIFICATION_2026-11-15.json) includes command logs and hashes,
module coverage, principal axiom reports and baseline comparisons. The raw
record is `.codex-work/v59-parameterized-substitution-20261115/incremental-verification/verification.json`,
SHA-256 `c9a03a18bede87c3b1903b1809c39eaf528ca547e7fb68ea83f290afd558bd2f`.

This completed incremental verification is **not a new full replay**. The
last completed [full v59 replay](V59_FULL_VERIFICATION_2026-11-14.md) remains
the 1,798-command run at `8df18834734179186459d3c4c34d4c0cf20b6194`.

## Remaining proof

Instantiate the PA internal derivation induction with the truth invariant
for every support covering the positive leaves. The same combined support
must serve both purported contradictory derivations. Discharge negative
leaves using PA disjointness, convert the all-model contradiction to the
PA theorem and the actual generated sentence-image consistency equation,
and identify the printed theory through its regular-image axiom subobject.
Finally prove the source inseparability clause and apply the existing
essential-incompleteness criterion with all extension quantifiers retained.
These obligations remain open, so the numbered lemma is not reclassified.
