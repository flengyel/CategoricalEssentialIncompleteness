# Parameterized formula component folds

Formula initiality is constructed in every numerical parameter slice, with
arbitrary target families. Fold uniqueness is also constructed across every
parameter morphism and every atom-label morphism. Proposition 10.7 remains
open: the concrete fork transition constructor squares and hence global
parameter-stable formula initiality are still pending. Stable variable
lists, substitution and finite derivation initiality remain open. The count
stays **74 of 77 numbered results proved**. Manuscript v59, its source, PDF,
archive and manifest remain unchanged.

## Constructed proof

`ForkFormulaParameterComponents` uses the existing two-sort numerical
parameterized initial algebra and projects to its formula sort. The actual
one-sort carrier is the constant family P × F_D, with its canonical
projection to P. The initiality proof covers every algebra carrier over P,
including nonconstant target families. The fold preserves both the
projection and the full five-branch constructor and is unique among all
algebra morphisms. Numerical variable, coefficient and parameter objects
are arbitrary, including empty carriers.

A change of parameter P → Q induces postcomposition from the slice over P
to the slice over Q. This functor preserves coproducts but need not preserve
relative products. `LaxPolynomialComparison` therefore constructs only the
forward polynomial comparison, using the canonical product comparison and
arbitrary coefficient morphisms. It proves naturality in both recursive
sorts and supplies the whole polynomial and joint comparisons. An inverse
product comparison or injectivity of coefficient morphisms is not assumed.

`LaxAlgebraAdjunction` uses this forward comparison and the postcomposition-
pullback adjunction to construct the right algebra. Its `mate_hom_iff`
identifies the original constructor equation with the algebra-morphism
equation under the adjunction. Initiality of the source then gives a unique
fold to every target algebra. `fold_natural` proves the generic criterion:
ordinary algebra morphisms commute with two coefficient transitions whose
constructor squares commute. This criterion does not assume that the
functor comparison is invertible.

`ForkFormulaParameterChange` instantiates the comparison for every
b:P → Q and every h:D → E. Both morphisms may identify labels. The variable
coefficient morphism has underlying morphism b × 1_N; the atom coefficient
morphism is b × h. The constructed fold is over b and satisfies the original
constructor equation. `underlying_unique` quantifies over all raw carrier
morphisms with the projection and constructor equations. The source
initiality and reindexed target evaluation are constructed, rather than
supplied as extra hypotheses of these instantiated results.

The independent Checks module states component initiality, its exact
constant-family carrier, arbitrary target families, the projection and
constructor equations, the two coefficient maps, all raw uniqueness
quantifiers and the generic naturality criterion. Four producers and their
Checks module pass five targeted strict elaborations and 19 principal
transitive axiom reports.

## Verification

Proof commit: `fab8223fd55efa813e437e4674f05edb33343f38`. All **17 incremental commands** passed,
including **9 strict elaborations**, the project build, both statement
audits, parser tests, manuscript gate and both complete transitive axiom
audits. The current audit covers **1,014 production modules**
and **30,452 declarations**. The retained audit covers
**1,274 declarations**. All 19 principal reports and both
complete audits use only `propext`, `Quot.sound` and `Classical.choice`.
All sixteen dependency worktrees remained clean and pinned;
356 source-provenance pins were checked. All
**2,537 measured inputs** remained unchanged and matched the proof
commit.

The controlled delta from the preceding completed incremental verification
contains five new Lean files, four production/audit entry points and the
selected correspondence table. Previous inputs were matched to their
published proof commit before comparison. The
[machine-readable record](V59_FORK_PARAMETER_COMPONENTS_VERIFICATION_2026-11-16.json) records command hashes, complete audit
coverage, principal reports, targeted checks and the source delta.
The raw record is
`.codex-work/v59-fork-parameters-20261116/incremental-verification/verification.json`,
SHA-256 `0e1894b846f65444662b9947630df16b06c4b353242ffb8a9f1b24e965e2dafc`.

This is completed **incremental verification of a partial proof batch**.
It does not complete Proposition 10.7 or the global parameter-stability
clause. The last completed
[full v59 replay](V59_FULL_VERIFICATION_2026-11-14.md) remains the
1,798-command run at `8df18834734179186459d3c4c34d4c0cf20b6194`.

## Remaining construction

Instantiate the generic naturality criterion with the actual fork
transitions. Prove the constructor square for the constant-family source
morphism P(j → k) × F_D(j → k), and the corresponding square for an arbitrary
natural target parameter algebra. These concrete squares remain open;
they are not assumptions of a completed Proposition 10.7. The resulting
component folds must then be assembled into the actual initial algebra
in every fork parameter slice.

Construct stable variable lists, the constant-variable decidable-equality
test, occurrence lists, admissible substitution and sentence objects. For
finite derivations, retain the seven logical schemes, two rules and ordered
premises, with arbitrary axiom subobjects in every parameter slice. Atom
transitions may identify labels, so equality of arbitrary formula labels
must not be assumed reflected by those transitions. Preserve subobject-only
initiality and generate arbitrary axiom presentations through regular
images. Propositions 10.7 and 10.8 and Corollary 10.9 remain open.
