# First-order fork formula initiality

The formula-initiality clause of Proposition 10.7 is constructed for every
nullary coefficient diagram. Proposition 10.7 remains open; the count stays
**74 of 77 numbered results proved**. Parameter stability, variable lists,
substitution and finite derivation initiality still require their full
fork constructions and independent checks. Manuscript v59, its source,
PDF, archive and manifest remain unchanged.

## Constructed proof

`DiagramInitialAlgebras` treats a diagram P of endofunctors. Given the
component initial algebras, it constructs a transition as the unique fold
into the coefficient-reindexed target algebra. Uniqueness proves the
identity and composition laws. A second use of uniqueness proves that
the component folds into every natural target algebra commute with all
transitions. The resulting algebra is initial in the actual diagram
category, with uniqueness among all natural algebra morphisms.

`SyntaxCoefficientMorphisms` constructs the action of a two-sort polynomial
on arbitrary coefficient morphisms. It proves naturality in the recursive
sorts, the identity law and composition. Coefficient morphisms may identify
labels. `NumericalDiagramSyntax` supplies the component initial algebras
from the existing numerical finite-tree construction, so the instantiated
result has no initiality or evaluation premise.

`ForkFirstOrderFormula` specializes to the constant full natural-number
variable diagram N and an arbitrary D in
WalkingSpan-to-numerical-tuples. Its polynomial is
Q_D(Y) = N² + D + Y + Y² + N × Y, with the displayed left association.
`polynomial_object` identifies all five summands. `polynomial_transition`
proves that a transition retains equality variables, acts by D's morphism
on atom labels, and acts by Y's morphism on each recursive child. The
quantifier retains the variable name. `numbers_full` and
`numbers_transition` prove the full carrier and identity transitions.

The component one-sort formula initiality is derived from the existing
two-sort numerical syntax initiality. Its unused first sort is mapped to
a terminal object. The general diagram construction then gives the actual
formula algebra and `initial` for every D. `fold_constructor`,
`fold_natural` and `fold_underlying_unique` state the constructor equation,
naturality under both fork transitions and uniqueness for every underlying
natural morphism satisfying that equation. No target operation is required
to extend to a globally total recursive operation on ambient numbers.

The independent Checks module states the full coefficient quantifiers,
object and transition formulas, variable-carrier equations and the raw
fold uniqueness statement. Four producers and their Checks module pass
five targeted strict elaborations and 24 principal transitive axiom reports.

## Verification

Proof commit: `38d7eae3581ca88d80bc07d1e41a0899bd5e065b`. All **17 incremental commands** passed,
including **9 strict elaborations**, the project build, both statement
audits, parser tests, manuscript gate and both complete transitive axiom
audits. The current audit covers **1,010 production modules**
and **30,373 declarations**. The retained audit covers
**1,274 declarations**. All 24 principal reports and both
complete audits use only `propext`, `Quot.sound` and `Classical.choice`.
All sixteen dependency worktrees remained clean and pinned;
356 source-provenance pins were checked. All
**2,532 measured inputs** remained unchanged and matched the proof
commit.

The controlled delta from the preceding completed incremental verification
contains five new Lean files, four production/audit entry points and the
selected correspondence table. Previous inputs were matched to their
published proof commit before comparison. The
[machine-readable record](V59_FORK_FIRST_ORDER_FORMULA_VERIFICATION_2026-11-16.json) records command hashes, complete audit
coverage, principal reports, targeted checks and the source delta.
The raw record is
`.codex-work/v59-fork-first-order-20261116/incremental-verification/verification.json`,
SHA-256 `cd98fe9b2086e5e71c1c2692972af1230db972ba453e9f33ec318ecb888512c4`.

This is completed **incremental verification of a partial proof batch**.
It does not complete Proposition 10.7. The last completed
[full v59 replay](V59_FULL_VERIFICATION_2026-11-14.md) remains the
1,798-command run at `8df18834734179186459d3c4c34d4c0cf20b6194`.

## Remaining construction

Prove parameter-stable initiality for the formula diagram in every fork
slice, including arbitrary target families. The existing numerical syntax
has the component parameterized initiality; the transition proof must
compare the component folds over changing parameter objects, using
pullback of the target family along each parameter transition.

Construct the stable variable lists and the decidable-variable test for
constant N. Assemble the occurrence, admissible-substitution and sentence
objects from those data. For finite derivations, retain the seven logical
schemes, two rules and ordered premises, with arbitrary axiom subobjects
in every parameter slice. Atom transitions may identify labels, so a
Boolean equality validator on the whole formula diagram must not be
assumed natural. Prove naturality of the typed derivation folds directly.
Preserve subobject-only initiality and generate arbitrary axiom
presentations through regular images. Propositions 10.7 and 10.8 and
Corollary 10.9 remain the three open numbered results.
