# WSL2 formalization against manuscript v59

Work in `/home/flengyel/src/CategoricalEssentialIncompleteness`.
Read `AGENTS.md`, `MANUSCRIPT_CURRENT.json`, `FORMALIZATION_STATUS_V59.md`
and `docs/V59_MANUSCRIPT_LEAN_CONTINUATION_2026-11-14.md`.

Version 59 corrects the bibliography publisher line break. All mathematical
text and all 77 numbered results and three definitions are unchanged from
v58. The reviewed v58 artifacts are retained. The Google report and its
assessment are in `docs/reviews/GOOGLE_V58_2026-11-14/`.

Theorem 5.3, Lemmas 8.9 and 9.6, and Corollaries 8.10 and 9.8 are complete.
Proposition 10.7 is also complete. The count is 75 proved results and two
open: 10.8 and 10.9. Proposition 10.8 is next. Preserve the
subobject-only initiality hypotheses, Boolean conventions and full extension
quantifiers. Preserve later local and remote work.

The positive-leaf assignment, primitive-recursive extraction and common finite
atom valuation are now constructed. See [the proof report](V59_SIGNED_DERIVATION_FINITE_SUPPORT_2026-11-14.md).
The [formula valuation](V59_BOOLEAN_FORMULA_VALUATION_2026-11-14.md) now has its five constructor laws, five logical
schemes, both inference rules and signed-atom values on arbitrary internal
supports. Its 19-command incremental verification is separate from the earlier
full replay. The later [parameterized substitution proof](V59_PARAMETERIZED_SUBSTITUTION_2026-11-15.md)
proves admissible-substitution invariance, full Option failure preservation
and all seven logical schemes. Its 25-command incremental verification is
separate from the full replay. The [internal truth proof](V59_INTERNAL_TRUTH_2026-11-15.md) now
excludes contradictory internal signed derivations in every PA model using
a common support. Its 23-command incremental verification includes both
complete axiom audits. The later [consistency proof](V59_SIGNED_CONSISTENCY_2026-11-15.md)
proves the PA sentence and generated signed-theory consistency equation
in the predicate category, with regular-image generation and a constructed
subobject-indexed proof family. Its 22-command incremental verification
includes both complete axiom audits. The later [diagonal signed-theory assembly](V59_DIAGONAL_SIGNED_THEORY_2026-11-15.md)
completes Lemma 8.9 through the proved predicate equivalence, with actual
split generators and all closed consistent extensions. Its 23-command
incremental verification includes both complete axiom audits. The later
[arithmetic associated-category proof](V59_ARITHMETIC_ASSOCIATED_CATEGORIES_2026-11-15.md) completes Corollary 8.10,
including arbitrary closed consistent slice extensions, both split Turing
categories, the literal full recursion subcategory and the specified original
arithmetic evaluator. Its 16-command final incremental verification includes both
complete axiom audits. The later [Miller parameterized-deduction proof](V59_MILLER_PARAMETERIZED_DEDUCTION_2026-11-15.md)
completes Lemma 9.6, including arbitrary nullary coefficients, numerical
variables, syntax/list stability and all printed signatures in every parameter
slice. Its 16-command incremental verification includes both complete axiom
audits. The later [Miller associated-category proof](V59_MILLER_ASSOCIATED_CATEGORIES_2026-11-15.md) completes
Corollary 9.8 with arbitrary slice extensions, actual domain inseparability,
the Boolean witness and every comparison functor. Its 22-command incremental
verification includes both complete axiom audits. The later
[first-order fork formula proof](V59_FORK_FIRST_ORDER_FORMULA_2026-11-16.md) constructs the initial formula
algebra for arbitrary coefficient diagrams, with the printed five summands
and unique natural folds under atom-identifying transitions. Its 17-command
incremental verification includes both complete axiom audits. At that
batch, Proposition 10.7 remained open. The later [parameterized component proof](V59_FORK_PARAMETER_COMPONENTS_2026-11-16.md)
constructs component formula initiality for arbitrary target families, fold
uniqueness across arbitrary parameter and atom-label morphisms, and the
generic transition-naturality criterion. Its separate 17-command incremental
verification includes both complete axiom audits. The later [natural parameter fold proof](V59_FORK_NATURAL_PARAMETER_FOLDS_2026-11-16.md)
proves the actual source constructor square, natural folds and initiality
among componentwise natural relative formula algebras for arbitrary target
families, and a canonical constant-family carrier isomorphism. Its separate
23-command incremental verification includes both complete axiom audits.
The later [canonical diagram syntax proof](V59_CANONICAL_DIAGRAM_SYNTAX_2026-11-16.md) constructs ordinary
initiality for the exact canonical two-sort polynomial, with an actual
polynomial isomorphism and algebra-category equivalence. It also constructs
decidable equality for the specified constant numerical-variable diagram.
Its separate 16-command incremental verification includes both complete
axiom audits. The later [slice evaluation and target folds](V59_SLICE_EVALUATION_TARGET_FOLDS_2026-11-16.md) construct the complete
slice polynomial comparison, transition squares for arbitrary recursive
families and natural folds into every canonical formula target. Component
constructor laws and raw uniqueness are proved; the 17-command incremental
verification includes both complete axiom audits. The later [canonical formula parameter-initiality proof](V59_CANONICAL_FORMULA_PARAMETER_INITIALITY_2026-11-16.md) closes the
source-constructor comparison and proves the full global constructor law,
initiality in every parameter slice and raw uniqueness for arbitrary target
families. Its separate 17-command incremental verification includes both
complete axiom audits. The later [full fork syntax proof](V59_FULL_FORK_SYNTAX_2026-11-16.md) constructs the complete
canonical term/formula bundle and parameter stability, stable lists,
the variable/term isomorphism, occurrences, admissible substitution and
sentence/admissibility pullbacks, naturally under all fork transitions.
Its 20-command incremental verification includes both complete axiom audits.
The later [fork parameterized deduction proof](V59_FORK_PARAMETERIZED_DEDUCTION_2026-11-17.md) completes
Proposition 10.7, including all seven schemes, both rules, arbitrary
parameter-dependent axiom subobjects, actual component constructor
isomorphisms, natural folds and raw uniqueness. Generation of arbitrary
presentations uses regular images. Its 18-command incremental verification
includes both complete axiom audits. The count is 75/77. Resume with
Proposition 10.8, on natural embedding/erasure, conservativity, consistency,
essential incompleteness and all endpoint extension conclusions, then
Corollary 10.9. Preserve actual carrier and constructor comparisons and
arbitrary closed consistent slice extensions. The WSL recovery archive
is retained as historical evidence.

The later [natural embedding and erasure proof](V59_FORK_EMBEDDING_ERASURE_2026-11-17.md) constructs
the actual propositional sentence embedding, all five erasure clauses,
the printed global tautology, retraction and monicity, with naturality
under atom-identifying transitions and the actual code comparisons.
Its 17-command incremental verification includes both complete axiom
audits. This is partial progress within Proposition 10.8; the count
remains 75/77. Resume with admissible-substitution erasure invariance,
then logical-rule and generated-theory comparisons, conservativity,
consistency, internal essential incompleteness and every endpoint
extension conclusion. Corollary 10.9 remains open. See the report for the
exact continuation point.

Use the existing serial build lock and pinned dependencies. Production
proofs and their dependencies must contain no proof placeholders; permitted
logical axioms are `propext`, `Quot.sound` and `Classical.choice`. The
designated isolated Palomar challenge declarations retain their exception.

Run from the repository root:

```bash
python3 scripts/test_verify_axiom_parser.py
python3 scripts/verify.py --manuscript-only
bash scripts/verify-wsl.sh
```

Record verification scope accurately. Commit completed changes to main and
push without force. Verify the live remote commit and current manuscript
version before reporting completion.
