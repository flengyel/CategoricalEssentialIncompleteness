# Slice evaluation and arbitrary canonical targets

Slice evaluation now compares the chosen global parameter polynomial with
its component polynomials for arbitrary recursive carrier families. The
comparison includes both sorts and commutes with every actual parameter
transition. Every canonical formula target algebra therefore receives the
proved natural component fold, including nonconstant target families, with
component constructor laws and uniqueness among all underlying natural
morphisms over the parameter diagram. The source constructor still needs
comparison with its canonical global parameterization before full canonical
parameter stability can be claimed. Proposition 10.7 remains open and the
count stays **74 of 77 numbered results proved**. Manuscript v59 is unchanged.

## Constructed proofs

`LaxPolynomialComparison.natural_square` proves coherence under a natural
transformation whose coefficient maps commute. It requires only forward
product comparisons. The intervening functor need not preserve products,
and the transformation and coefficient maps need not be monic or invertible.

`SliceEvaluation` constructs evaluation `Over P → Over (P.obj j)` using
`Over.post`. Finite-limit and finite-coproduct preservation are proved.
Evaluation of a global chosen constant family is canonically isomorphic
to the chosen component constant family. Compatibility with every actual
parameter transition is proved from the product projection naturality laws.

`SlicePolynomialComparison` constructs the polynomial evaluation
isomorphisms and the complete two-sort natural isomorphism. It identifies
the exact `withParameters` expression, proves the parameter-transition
square for arbitrary recursive families, and derives component operation
naturality from any actual global polynomial operation. The coefficient
compatibility needed by the generic coherence theorem is discharged by the
proved constant-family square. These instantiated results have no extra
component constructor-square hypothesis.

`ForkCanonicalParameterTargets` identifies its global target functor with
the exact canonical parameterized five-branch formula expression. Every
canonical target algebra induces a natural relative component algebra,
with operation naturality proved by the preceding theorem. The existing
concrete source square and natural component folds then give a fold to
every such target. It preserves the parameter projection and all component
constructors. Raw uniqueness includes every underlying natural morphism
satisfying those equations. The canonical constant-family carrier also
maps naturally to each target through the proved carrier isomorphism.

These are not yet the full global constructor equation for the
parameterization of the original global source algebra. That source
comparison and the full two-sort parameterized initiality assembly remain
open. Independent checks retain this scope and all arbitrary-target and
raw-morphism quantifiers.

## Verification

Proof commit: `b06ebaf0038c40018e220ceb6b2cfc9074e4ab97`.
All **17 incremental commands** passed, including **9 strict elaborations**,
the project build, both statement audits, parser tests, manuscript gate
and both complete transitive axiom audits. The current audit covers
**1,027 production modules** and
**30,798 declarations**; the retained audit covers
**1,274 declarations**. The selected Checks module reports
**31 principal declarations**. All principal reports and both complete
audits use only `propext`, `Quot.sound` and `Classical.choice`.
All sixteen dependency worktrees remained clean and pinned, and
356 provenance pins passed. All
**2,553 measured inputs** remained unchanged and matched the proof commit.

Five selected producer/Checks sources also passed a separate targeted
strict run with a 2 GB Lean memory bound. Integrated strict checks used
3 GB. Runs used the existing serial build lock, one Lean thread and explicit
timeouts. No prior production proof or dependency was modified.
The measured delta from the preceding incremental snapshot is ten files:
four new producers, one new Checks module, four production/audit entry
points and the correspondence table. Previous measured inputs were matched
to their published proof commit. The WSL recovery archive and reviewed v58
artifacts remain unchanged.

The [machine-readable record](V59_SLICE_EVALUATION_TARGET_FOLDS_VERIFICATION_2026-11-16.json) records command hashes, source delta,
module coverage, principal reports and targeted results.
Raw record: `.codex-work/v59-slice-evaluation-20261116/incremental-verification/verification.json`;
SHA-256 `591e9f885c43522448fbb4ad8151880b11ff5476d02f102a054a2a155f22e147`.
This is **completed incremental verification of a partial proof batch**.
The last completed [full v59 replay](V59_FULL_VERIFICATION_2026-11-14.md)
remains the 1,798-command run at
`8df18834734179186459d3c4c34d4c0cf20b6194`.

## Resume point

Compare the canonical global source parameter constructor with the actual
numerical component parameter constructors under the new evaluation and
coefficient isomorphisms. Derive the full global constructor equation for
the constructed folds; do not add source compatibility as a hypothesis.
Assemble the full two-sort parameterized initiality using the actual term
and formula carriers and their constructor comparisons. Reuse the proved
ordinary canonical initiality, the natural source reindexing square and
the arbitrary canonical target extraction constructed here.

Stable variable lists, occurrence lists, admissible substitution, sentence
objects and seven-scheme, two-rule finite derivation initiality remain open.
Require derivation initiality only for axiom subobjects, generate arbitrary
axiom presentations through regular images, and preserve the Boolean
conventions and full extension quantifiers. Propositions 10.7 and 10.8 and
Corollary 10.9 remain open.
