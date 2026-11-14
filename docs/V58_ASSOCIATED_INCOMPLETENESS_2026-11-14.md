# Theorem 5.3 complete against manuscript v58

The full essential-incompleteness equivalence and final reduction clause are
proved at `7a07264ce4137e0c539f02b30faf4d2a709fb309`. The count is **70 of 77 numbered results proved**, with
seven open obligations. Lemma 8.9 is next. Manuscript v58 is unchanged.

## Construction and statement correspondence

The [proof outline](V58_THEOREM_5_3_PROOF_OUTLINE_2026-11-14.md) maps the five
required steps to the existing interfaces. Eight new producer modules and
`V46AssociatedIncompletenessChecks` construct and check the remaining clauses.

`SliceSubobjectPredicates.orderIso` identifies the actual predicate lattice
of an ordinary slice object with its underlying subobject lattice. Constant
families are second-projection pullbacks. Evaluation of an arbitrary slice
predicate is its point-fiber pullback; `SliceEvaluationSubobjects` identifies
this with ordinary evaluation followed by the retraction component. Meet,
join, bottom, top and refutation equations prove consistency and completeness
preservation. No constancy assumption is placed on the slice predicate.

`RetractedRuleComparison.translation` maps the original nullary, unary and
binary rule instances into evaluated slice rules. Its product comparisons
use inverse natural-retraction components; its axiom component uses the
actual evaluated axiom subobject. `RetractedClosedTheories.closed_back`
constructs the mapped closed formula algebra, reindexes along this rule
translation, and folds the original initial derivation algebra into it.
The sentence pullback identifies the resulting closed base theory.

`AssociatedClosedTheories` uses the existing `FirstOrderPresentation` and
its `Theories`, `Consistent`, `Complete` and `EssentiallyIncomplete` on the
base. The slice system is the literal constant sentence family, transported
logical operations and rule labels. All initiality binders are axiom
subobjects. Generation from an arbitrary axiom morphism remains the existing
`presentationGeneration` through its regular image; the independent check
asserts that formula. No closure, consistency, completeness or incompleteness
conclusion is introduced as a hypothesis, and neither functor is assumed to
preserve initial algebras.

The forward implication evaluates **every** closed consistent complete slice
extension above B(u) into the original calculus. The retraction identifies
its inclusion above u. The reverse implication sends each base extension
forward by B. The statement check expands the slice quantifier to arbitrary
subobjects W with Gen(W)=W; it requires no constant-family witness.

`AssociatedCategory.associated_incompleteness` combines the equivalence with
the existing actual partial-slice Boolean-morphism results and retraction.
`essential_incomplete_of_reduction` and `associated_reduction` prove the final
clause for every consistent closed extension receiving the printed total
subobject reduction bounds. The existing no-total-extension theorem is reused.
`AssociatedSliceCoordinates.comparison` constructs the canonical natural
isomorphism from chosen categorical products to the restriction products used
by the existing actual partial-slice functor. Its `theory_value` identifies
the theorem subobject, `actual_map` identifies the actual partial constant
map on total morphisms, and `evaluation_total` identifies its evaluation.
Independent checks include the existing `sourceTheory` morphism itself.
The complete-statement check also asserts the source restriction-idempotent
inseparability formulation. The fixed logical theorem supplies the point
only on theories under consideration; there is no global-element hypothesis
for arbitrary objects or complementedness requirement on that point.

## Verification scope

All **25 incremental commands passed**, including
**17 strict elaborations**. These cover the eight
new producers, independent complete-statement check, selected existing
interfaces, project build, both statement entry points, parser tests,
manuscript gate and both complete transitive axiom audits. Separate targeted
verification also passed its ten commands. The complete-statement check
prints and verifies 23 principal transitive axiom reports.

The current audit covers **935 production
modules and 28,620 declarations**; the retained
audit covers **1,274 declarations**. The complete
axiom union is exactly `propext`, `Quot.sound`, `Classical.choice`. All sixteen
dependencies were clean and pinned at both ends; all imported-source checks
passed. All 2428 tested inputs matched the proof commit
and stayed unchanged throughout verification.

Only the correspondence table changes after this successful run, to record
Theorem 5.3 complete. The [record](V58_ASSOCIATED_INCOMPLETENESS_VERIFICATION_2026-11-14.json) identifies its tested and final hashes.
All Lean, manuscript, dependency and verification-script bytes remain the
tested bytes; the manuscript gate is rerun on the final correspondence.
Earlier full and incremental runs are preserved separately. This report does
not claim that a new full replay has completed.

Raw evidence: `.codex-work/v58-associated-incompleteness-20261114/incremental-verification-2`.
Verification JSON SHA-256: `bb38925bceea57b1dd831aa13e41c26ef4dea1c2f8bb5ed59dacd66f9ac6e639`.
