# Boolean formula valuations for Lemma 8.9

Five producers and two independent Checks modules extend the finite atom
assignment to a formula valuation with its support retained as an internal
parameter. The five formula-constructor equations, five logical schemes,
both inference rules and signed-atom values are proved. Lemma 8.9 remains
open. The count is **70 of 77 numbered results proved**, with seven open;
Theorem 5.3 remains complete. The manuscript v59 bytes are unchanged.

## Construction

Let D be a regular finitary extensive category, P a parameter object and X
the nullary-predicate label object. Write c_P(X) for `constantFamily P X`
and 2 for `Two D`. For the supplied nullary syntax S, let F be its formula
object. `ParameterizedBooleanValuation.algebra` accepts an arbitrary
assignment d : c_P(X) → c_P(2) in D/P. The term carrier is terminal; equality
has value true, negation and implication use the existing Boolean operations,
and quantification is the second projection. The actual stable initial fold
constructs v : c_P(F) → c_P(2), hence a total morphism P × F → 2 in D.
`NullarySyntaxAlgebraHom` proves the six constructor equations for arbitrary
algebra morphisms, including with an arbitrary empty-function coefficient.
Those equations and the existing parameter-constructor comparisons prove the
five valuation laws. Chosen products and coproducts are compared by the
specified morphisms rather than identified with numerical carriers.

`ParameterizedBooleanEquations` proves the laws with a shared parameter
p : W → P and arbitrary formula morphisms W → F. Thus the calculations
apply over arbitrary input families. `ParameterizedBooleanLogical` proves
the three propositional schemes, quantifier distribution and equality
reflexivity at that parameter, together with truth propagation by modus
ponens and generalization.

`SignedFiniteFormulaValuation` sets P to the constructed internal list
object for X. Its atom assignment uses the existing numerical membership
morphism and its proved comparison to the actual Boolean object. One total
morphism evaluates formulas at all supports. Its atom and negated-atom
computations hold in every PA model, including for nonstandard internal
lists. A member of the support makes its positive atom true. An absent
label makes its negative atom true. `diagonal_negative_axiom` combines
this computation with the proved PA disjointness theorem: a beta-label makes
its negative axiom true on every alpha-support. No consistency or
incompleteness conclusion is used as a hypothesis.

The independent checks state the constructed morphisms and their full
constructor, scheme, inference and signed-atom equations. A concrete check
constructs both the no-function/nullary-predicate PA syntax and its valuation
from the existing plain syntax construction, with no syntax-existence
hypothesis. The new producers are imported by the production entry point
and the complete axiom audit; both statement-audit entry points include the
new Checks files.

## Verification

The proof commit is `e3d669ba3f299db26451fc1d1c76862148a06fff`. All **19 incremental commands**
passed, including **11 strict elaborations**, the integrated build, both
statement audits, parser tests, manuscript gate and both complete transitive
axiom audits. The current audit covers **951 production modules**
and **29,080 declarations**; the retained audit covers **1,274**.
All **38 principal axiom reports** and both complete audits use only
`propext`, `Quot.sound` and `Classical.choice`. All 16 dependency worktrees
were clean and pinned at both ends; 356 source-provenance pins were checked.

All **2,452 measured inputs** remained unchanged and matched the
proof commit. The controlled delta from the prior 21-command incremental
verification consists of the seven new Lean files, four production/audit
entry points and the active correspondence row. The earlier full v59
baseline and the prior incremental baseline were each independently matched
to their published proof commits before comparing their inputs.

The [machine-readable record](V59_BOOLEAN_FORMULA_VALUATION_VERIFICATION_2026-11-14.json) records command logs, hashes, module
coverage, principal axiom reports and both baseline comparisons. The raw
local verification record is
`.codex-work/v59-boolean-formula-20261114/incremental-verification/verification.json`;
its SHA-256 is `0c9d7ac21fd451fca0a5296bf21fb2476fad9af0b343a6c6155d9caf8cc8efd1`.

This is a completed incremental verification, **not a new full replay**.
The last completed [full v59 replay](V59_FULL_VERIFICATION_2026-11-14.md)
remains the 1,798-command run at
`8df18834734179186459d3c4c34d4c0cf20b6194`.

## Remaining proof

Prove admissible-substitution invariance while retaining both the support
parameter and the actual binder/replacement parameters. The existing
fixed-assignment equalizer proof supplies the pattern, including the
equal-binder and capture branches. The instantiation and equality-substitution
schemes then need their parameterized valuation laws.

Next instantiate `InternalInduction.model_rule_induction` with the internal
truth invariant: every support covering the positive leaves makes the
conclusion true, with the negative-label condition discharged by PA
disjointness. Both proposed contradictory derivations must use the same
combined support. Convert the all-model contradiction to the PA theorem
and the actual generated sentence-image consistency equation. Identify the
printed signed theory through its regular-image axiom subobject, prove the
source inseparability clause and apply the existing essential-incompleteness
criterion with every extension quantifier retained. These are still open
obligations; the numbered lemma is not reclassified.
