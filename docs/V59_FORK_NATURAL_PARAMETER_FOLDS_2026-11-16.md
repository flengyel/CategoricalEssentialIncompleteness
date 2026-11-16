# Natural parameterized fork formula folds

The actual fork source constructor square is proved. Formula folds are
natural and unique for arbitrary target families in the category of
componentwise natural relative formula algebras. Initiality is constructed
in that category, with a canonical isomorphism from its pointwise product
carrier to the specified constant-family carrier. This is partial progress
toward Proposition 10.7. Its canonical global two-sort syntax interface,
variable lists, substitution and derivations remain open. The count stays
**74 of 77 numbered results proved**. Manuscript v59 and its artifacts are
unchanged.

## Proof and scope

The labelled polynomial comparison commutes with arbitrary parameter,
coefficient and recursive morphisms. Distinct labels remain distinct even
when their coefficient objects coincide. Only the forward product
comparison is used. No product preservation, invertibility or injectivity
is assumed.

`ForkFormulaSquareTransport` first proves constructor transport for
arbitrary algebra records. `ForkFormulaTransitionSquares.fork_source_square`
then applies it to the actual numerical formula algebras and fork
transitions, using the previously proved unparameterized constructor law.
The concrete source square has no supplied compatibility premise.

`ForkParameterizedFormulaFolds.Algebra` has an arbitrary carrier over P
and the five printed relative constructor operations. Naturality of those
operations defines an algebra in this category. The source operations
satisfy that condition by the proved concrete square. Component initiality
and the generic lax fold criterion prove naturality of every target fold.
The resulting global fold preserves the projection and all constructors.
Uniqueness covers every underlying natural carrier morphism with those
equations. D and P are arbitrary diagrams; target families need not be
constant, and atom transitions may identify labels.

`parameterCarrierIso` is the canonical product isomorphism over P to the
chosen constant family. This carrier comparison does not yet identify the
constructed algebra category with the canonical global two-sort
`SyntaxPolynomial`/`CategoricalSyntax` parameter interface. That comparison
remains a proof obligation.

The numerical `pairAlgebra` uses Mathlib's `irreducible_def` to control
kernel reduction. Its equation theorem retains exactly the original
`NumericalSyntax.data` value. Existing initiality and parameter stability
are recovered through that equation. Independent checks include this exact
equation, the unconditional source square, arbitrary targets, the carrier
isomorphism, fold equations and full underlying uniqueness quantifier.
No mathematical value, printed hypothesis, dependency or permitted axiom
is changed.

## Verification

Proof commit: `657efd171892e12adc973f4d0fc08a7471265fce`.
All **23 incremental commands** passed, including **15 strict elaborations**,
the project build, both statement audits, parser tests, manuscript gate
and both complete transitive axiom audits. The current audit covers
**1,020 production modules** and
**30,654 declarations**; the retained audit covers
**1,274 declarations**. The three selected Checks modules
report **71 distinct principal declarations**. Both complete audits and
all principal reports use only `propext`, `Quot.sound` and `Classical.choice`.
All sixteen dependency worktrees remained clean and pinned, and
356 provenance pins passed. All
**2,544 measured inputs** remained unchanged and matched the
proof commit.

The selected targeted checks passed **11 strict elaborations** at a 2 GB
Lean memory bound. Integrated strict checks used a 3 GB bound. All compiler
runs were serial under the build lock with one Lean thread and explicit
timeouts. Earlier diagnostic timeouts are not successful verification.
The first integrated attempt detected a generated instance-name collision
between the new Checks module and an existing one. The new module now has
its own namespace; strict checking and both statement-audit builds passed
before the final integrated run was restarted. That failed attempt is
retained at `.codex-work/v59-wsl-resume-20261116/incremental-verification-initial-name-collision/`.
It is excluded from the successful command count.
The WSL failure itself has not been diagnosed.

The measured delta from the previous completed incremental snapshot is
fourteen files: six new producers, one new Checks module, two modified
producers, four production/audit entry points and the correspondence table.
Previous measured inputs were matched to their published proof commit.
The [machine-readable record](V59_FORK_NATURAL_PARAMETER_FOLDS_VERIFICATION_2026-11-16.json) includes command hashes, complete
module coverage, principal reports, targeted results and the controlled delta.
Raw record: `.codex-work/v59-wsl-resume-20261116/incremental-verification/verification.json`;
SHA-256 `f4d1f5244fce93f56692a778ea3cfa5116af5238ee608a3a2a238ca7c8e2640e`.

This is completed **incremental verification of a partial proof batch**.
The last completed [full v59 replay](V59_FULL_VERIFICATION_2026-11-14.md)
remains the 1,798-command run at
`8df18834734179186459d3c4c34d4c0cf20b6194`.
The [WSL recovery checkpoint](V59_WSL_RECOVERY_2026-11-16.md) and all five
archived drafts and eight logs are retained verbatim as historical evidence.

## Resume point

Compare the constructed natural relative formula algebra with the canonical
global two-sort parameter interface. Construct stable variable lists and
the constant-variable decidable-equality test, then occurrence lists,
admissible substitution and sentence objects. Construct seven-scheme,
two-rule finite derivation initiality for axiom subobjects in every
parameter slice, retaining ordered premises. Arbitrary axiom presentations
generate through their regular images. Preserve the Boolean conventions
and full extension quantifiers. Propositions 10.7 and 10.8 and Corollary
10.9 remain open.
