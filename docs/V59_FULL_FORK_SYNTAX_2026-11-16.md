# Full fork syntax, stable lists and substitution

The complete `CategoricalSyntax` bundle is constructed for the printed
fork language: numerical variables, no function symbols and arbitrary
nullary coefficient diagram D. Its exact canonical two-sort algebra is
initial in every global parameter slice, for all target families. Stable
variable lists, the variable/term isomorphism, occurrence lists, admissible
substitution and sentence objects are constructed. The occurrence and
substitution morphisms commute with every fork transition, including
transitions that identify atom labels.

Proposition 10.7 remains open for initial finite derivation algebras for
the seven schemes and two rules in every parameter slice. The count is
**74 of 77 numbered results proved**; 10.7, 10.8 and 10.9 remain open.
Manuscript v59, its source, PDF, archive and manifest are unchanged.

## Construction

`LabelledParameterAlgebras` retains each polynomial together with its
parameter comparison. Structural induction proves equality with the
actual canonical comparison and then equality of the complete algebras.
This handles all coefficient positions and both recursive sorts, without
replacing a constructor comparison by an assumption.

`DiagramParameterConstructor` applies the proved comparison square to
every ordinary constructor. `SliceAlgebraInitiality` assembles local
initial folds into global morphisms over the parameter. Naturality follows
from local uniqueness, the actual operation squares and the product of
the pullback adjunctions. Only the forward polynomial comparison is used
for changes of parameter. Individual component evaluations are not
assumed faithful; global equations are checked at every component.

`NumericalDiagramParameterStability` identifies the actual global source
with the stable numerical component sources and proves the full global
constructor law and uniqueness. Its `data` construction returns the
exact canonical term/formula algebra, ordinary initiality and initiality
over every global parameter. Targets may be nonconstant families.
The existing numerical component algebra has an equation-controlled
reduction guard; its original definition, initiality and parameter
stability are recovered by proved equations. No dependency was changed.

`DiagramStableLists` projects a list algebra from the two-sort initial
algebra and proves agreement of both actual parameter constructors.
It supplies stable lists for arbitrary numerical diagrams.
`ForkCategoricalSyntax.categoricalSyntax` assembles the complete bundle
for the specified nullary language. The actual variable constructor is
an isomorphism. Existing categorical recursion then supplies occurrence
lists and admissible substitution as global morphisms. Empty occurrences
define the sentence pullback; successful substitution defines the
admissibility pullback along the second coproduct injection. The original
carrier invariant is retained. Truth remains the second Boolean injection,
and the existing quantifier convention is unchanged.

The construction uses the canonical two-sort carriers. It does not claim
that separately constructed numerical formula code charts are identical.
Any use of those other realizations must retain actual carrier and
constructor isomorphisms. Initial finite derivations are still required
only for axiom subobjects; arbitrary presentations generate through
their regular images.

## Verification

Proof commit: `5dab6347ce64c0a2e756ce81f939606c53b1028c`.
All **20 incremental commands** passed, including **12 strict
elaborations**, the project build, both statement audits, parser tests,
the manuscript gate and both complete transitive axiom audits. The current
audit covers **1,037 production modules**
and **30,983 declarations**; the retained audit
covers **1,274 declarations**. Independent
`V46ForkCategoricalSyntaxChecks` includes **34 principal axiom reports**.
All principal reports and both complete audits use only `propext`,
`Quot.sound` and `Classical.choice`.

All sixteen dependency worktrees remained clean and pinned, and
356 provenance pins passed. All
**2,565 measured inputs** remained unchanged and
matched the proof commit. The measured delta is thirteen files: six new
producers, one Checks module, one updated numerical producer, four
production/audit entry points and the correspondence table. Previous
inputs were matched to their published proof commit.

The eight changed producer/Checks sources also passed separate targeted
strict checks at 2 GB with a 120-second command limit. Integrated strict
checks used 3 GB and explicit 600-second command limits. Runs used the
serial build lock and one Lean thread. Bounded development failures and
interrupted checks are excluded from successful verification counts.
The historical WSL recovery archive and reviewed v58 artifacts are
retained verbatim.

The [machine-readable record](V59_FULL_FORK_SYNTAX_VERIFICATION_2026-11-16.json) contains source and command hashes,
module coverage, principal reports and targeted results. Raw record:
`.codex-work/v59-full-syntax-20261116/incremental-verification/verification.json`;
SHA-256 `44aa9d592cebee50397cdd4290077f2445312b0c22d48016c1601b86ec2ee2bb`.

This is completed **incremental verification**, and partial progress on
Proposition 10.7. No new full replay was run. The last completed
[full v59 replay](V59_FULL_VERIFICATION_2026-11-14.md) remains the
1,798-command run at `8df18834734179186459d3c4c34d4c0cf20b6194`.

## Resume point

Start with the inference endofunctor for the actual
`ForkCategoricalSyntax.categoricalSyntax D`: all seven logical schemes,
modus ponens and generalization, with an axiom subobject of the sentence
object over each arbitrary parameter. Construct the numerical component
derivation sources and their actual transition constructor squares,
natural evaluation and uniqueness. Reuse the existing numerical
derivation infrastructure and the now completed two-sort syntax, lists,
occurrence and substitution interface. Keep carrier and constructor
comparisons explicit when using different numerical realizations.
Relabelling must preserve premise matching and side conditions; it need
not reflect atom-label equality. Do not add initiality for arbitrary
axiom morphisms. Pass arbitrary presentations through their regular
images. Then continue Proposition 10.8 and Corollary 10.9, retaining
the full consistent-extension quantifiers and completed Theorem 5.3.
