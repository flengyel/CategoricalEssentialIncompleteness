# Corollary 9.8: Miller associated categories

Corollary 9.8 is complete. The count is **74 of 77 numbered results proved**.
Proposition 10.7 is next. Manuscript v59, its source, PDF, archive and
manifest remain unchanged.

## Constructed proof

Let a be a Miller sequence and write D_a = Tot(Split(E_a)).
`Miller.AssociatedData` uses the actual canonical ordered-field syntax of
Theorem 9.7. The base theory is the regular image of its chosen sentence
conclusion for the expanded real-closed field axioms. Initial proof
algebras are required only for axiom subobjects. The existing generation
of arbitrary axiom presentations through regular images is retained.

The closed sentence 0 = 0 gives a morphism from a terminal object to the
sentence object. Its instance of the sixth logical scheme factors through
every closed internal theory. `point_factors` constructs this common
logical theorem point, which supplies the section used in the existing
constant-family retraction.

`RestrictionSubobjects.domain_pullback` and `domain_image` identify the
actual subobject domains with the restriction ranges used in Theorem 9.7.
`Miller.AssociatedTheories.global_incompleteness` consequently covers every
closed internal extension of the actual generated base theory with only
the printed Miller-sequence, extension and consistency hypotheses.

`Miller.AssociatedIncompleteness.constantTheory` constructs the closed
theory 1_U × u in D_a/U from the completed parameterized proof algebras.
Evaluation at the common theorem point proves incompleteness for every
closed consistent slice extension, including nonconstant families.
`SliceInseparability.constant` excludes arbitrary complementary slice
separators. The full canonical subobject equivalence with the total
category of the actual Par(D_a/U) transfers theorem/refutation
inseparability. `actual_essentially_incomplete` excludes a consistent
complete extension among all subobjects of that actual total category;
its quantifier therefore includes every closed consistent extension.

`Miller.AssociatedStructure.turingData` constructs compatible binary
products, a universal evaluator, total restriction embeddings of every
actual slice object, a restriction terminal object and splittings in
Par(D_a/U). `NativeSplitSlices` proves the required comparison of the
native Miller restriction structure with the product-induced structure.
The original uniform recursion-category construction is reused; no
representation is selected or replaced by an ordinary recursive target.

The Boolean partial morphism has domain u ∨ ν*u, is true on u and false
on ν*u. Its actual constant-family image has the corresponding domain and
values. The proved inseparability criterion and both directions of the
existing total-extension retraction exclude a total extension there.
True remains the second coproduct injection; the existing second-projection
quantifier convention is preserved.

For every consistent closed target theory and every monic theory inclusion,
the actual postcomposition functor is full, faithful and restriction
preserving. A proper inclusion excludes essential surjectivity. These
properties are constructed from the existing general partial-slice
results. `Miller.AssociatedCategories.printed_statement` assembles every
printed conclusion without assuming preservation, deduction initiality
or incompleteness as an extra hypothesis.

The two independent Checks modules state the complete hypotheses and
quantifiers, expand the full Turing structure, and check the domain,
Boolean-value and comparison-functor clauses. The prerequisite batch was
published at `d6822f3f14a31e60139ff55c536eadc27e79af5f`. Across both batches,
eight producers and two Checks modules passed ten targeted strict
elaborations and 49 principal axiom reports before the final proof commit.

## Verification

Proof commit: `a6d5023e1664e9065c97f053e7bb60aa6b31e5d3`. All **22 incremental commands** passed,
including **14 strict elaborations**, the project build, both statement
audits, parser tests, manuscript gate and both complete transitive axiom
audits. The current audit covers **1,006 production modules**
and **30,273 declarations**. The retained audit covers
**1,274 declarations**. All 49 principal reports and both
complete audits use only `propext`, `Quot.sound` and `Classical.choice`.
All sixteen dependency worktrees remained clean and pinned;
356 source-provenance pins were checked. All
**2,527 measured inputs** remained unchanged and matched the proof
commit.

The controlled delta from the preceding completed incremental verification
contains ten new Lean files, four production/audit entry points and the
selected correspondence table. Previous inputs were matched to their
published proof commit before comparison. The
[machine-readable record](V59_MILLER_ASSOCIATED_CATEGORIES_VERIFICATION_2026-11-15.json) records command hashes, complete audit
coverage, principal reports, both targeted batches and the source delta.
The raw record is
`.codex-work/v59-miller-associated-20261115/incremental-verification/verification.json`,
SHA-256 `cb7a91a561d6fb33c49b012850f9c68bde3fe88b67fd83e2c404b01cff7384d7`.

This is completed **incremental verification**. The last completed
[full v59 replay](V59_FULL_VERIFICATION_2026-11-14.md) remains the
1,798-command run at `8df18834734179186459d3c4c34d4c0cf20b6194`.

## Next obligation

Proposition 10.7 requires first-order fork syntax with arbitrary nullary
coefficient objects and initial finite-derivation algebras in every
parameter slice. Construct componentwise folds, prove naturality under
both transitions, including transitions that identify atom labels, and
prove uniqueness among all algebra morphisms. Propositions 10.7 and 10.8
and Corollary 10.9 are the three remaining numbered obligations. Preserve
the constant numerical-variable diagram, subobject-only initiality and
all extension quantifiers.
