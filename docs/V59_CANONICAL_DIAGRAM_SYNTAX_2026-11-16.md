# Canonical diagram syntax and variable equality

Ordinary initiality is constructed for the canonical global two-sort
polynomial on numerical diagrams, with arbitrary coefficient diagrams and
polynomial templates. The exact `termExpression` and `formulaExpression`
of the syntax interface are covered. Decidable equality is also constructed
for the actual constant numerical-variable diagram. Proposition 10.7 remains
open: canonical parameter stability, stable lists, substitution and
derivations still require construction. The count remains **74 of 77
numbered results proved**. Manuscript v59 and its artifacts are unchanged.

## Constructed proofs

`DiagramPolynomialComparison` constructs an isomorphism between evaluating
the chosen functor-category polynomial at an index and evaluating the
literal component polynomial. It preserves the product projections and
coproduct branches. Its naturality theorem includes every coefficient
transition and both recursive carrier transitions. Template labels remain
separate when their coefficient objects coincide. No injectivity or
reflection of label equality is assumed.

`NumericalCanonicalDiagramSyntax.polynomialIso` combines those comparisons
with the equivalence between a pair of functors and a functor into a product
category. It compares the complete canonical polynomial with the existing
componentwise polynomial functor, naturally in both recursive carriers.
The resulting equivalence of algebra categories includes every algebra
morphism. The existing numerical diagram initial algebra is lifted through
this equivalence. `constructorIso` compares its constructor with the original
one. The constructed fold satisfies the full constructor equation and is
unique among all underlying pairs of natural carrier morphisms satisfying
that equation.

`syntaxData` specializes this construction to the exact canonical term and
formula expressions at arbitrary finite signature bounds. Independent
checks also instantiate the printed fork signature: the full constant
numerical-variable diagram, no function symbols and arbitrary nullary
predicate diagram D. This supplies ordinary initiality; it does not yet
supply the canonical parameter-stability field or a complete
`CategoricalSyntax` bundle.

`DiagramDecidableVariables` transports the diagonal pullback under a
functor preserving finite limits and finite coproducts. Its constant-functor
instance constructs decidable equality for the specified variable diagram.
The independent pullback check explicitly uses the second Boolean injection
as truth. This construction concerns variables and makes no assertion of
natural decidable equality for arbitrary atom labels.

## Verification

Proof commit: `8c518d7585b1b9677a521db9611321e5e5a1773f`.
All **16 incremental commands** passed, including **8 strict elaborations**,
the project build, both statement audits, parser tests, manuscript gate
and both complete transitive axiom audits. The current audit covers
**1,023 production modules** and
**30,736 declarations**; the retained audit covers
**1,274 declarations**. The selected independent Checks
module has **31 principal axiom reports**. Both complete audits and all
principal reports use only `propext`, `Quot.sound` and `Classical.choice`.
All sixteen dependency worktrees remained clean and pinned, and
356 provenance pins passed. All
**2,548 measured inputs** remained unchanged and matched the
proof commit.

The four selected producer/Checks sources also passed a separate targeted
strict run with a 2 GB Lean memory bound. Integrated strict checks used
3 GB. Runs used the existing serial build lock, one Lean thread and explicit
timeouts. No dependencies or prior production proofs were modified.
The measured delta from the preceding incremental snapshot contains nine
files: three new producers, one new Checks module, four production/audit
entry points and the correspondence table. Previous measured inputs were
matched to their published proof commit. The historical WSL recovery
archive and reviewed v58 artifacts remain unchanged.

The [machine-readable record](V59_CANONICAL_DIAGRAM_SYNTAX_VERIFICATION_2026-11-16.json) contains command hashes, source delta,
module coverage, principal reports and targeted results.
Raw record: `.codex-work/v59-diagram-polynomial-20261116/incremental-verification/verification.json`;
SHA-256 `0e62c1be5f8a99a25dec4946fed28c73c88084e2eff700b00727d65e7af7566b`.
This is **completed incremental verification of a partial proof batch**.
The last completed [full v59 replay](V59_FULL_VERIFICATION_2026-11-14.md)
remains the 1,798-command run at
`8df18834734179186459d3c4c34d4c0cf20b6194`.

## Resume point

Construct the comparison for the canonical parameterized two-sort algebra
and prove its initiality for arbitrary target families in every slice.
Reuse the proved [natural parameterized folds](V59_FORK_NATURAL_PARAMETER_FOLDS_2026-11-16.md),
while comparing the actual constructors and carriers. The ordinary
polynomial isomorphism does not by itself discharge this slice obligation.
Start with evaluation `Over P → Over (P.obj j)`, induced by `Over.post`.
Construct its chosen finite-product and finite-coproduct comparisons,
including the coefficient isomorphism from evaluation of the global
constant family to the component constant family. Prove commutation with
the parameter transitions for arbitrary recursive target families. The
existing concrete source square and raw fold uniqueness must be reused;
the target's operation naturality is part of its algebra structure.
Construct stable variable lists, occurrence lists, admissible substitution
and sentence objects. Then construct seven-scheme, two-rule finite
initial derivation algebras for axiom subobjects in every parameter slice.
Generate arbitrary axiom presentations through their regular images.
Preserve the Boolean conventions and full extension quantifiers.
Propositions 10.7 and 10.8 and Corollary 10.9 remain open.
