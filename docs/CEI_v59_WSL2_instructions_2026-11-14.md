# WSL2 formalization against manuscript v59

Work in `/home/flengyel/src/CategoricalEssentialIncompleteness`.
Read `AGENTS.md`, `MANUSCRIPT_CURRENT.json`, `FORMALIZATION_STATUS_V59.md`
and `docs/V59_MANUSCRIPT_LEAN_CONTINUATION_2026-11-14.md`.

Version 59 corrects the bibliography publisher line break. All mathematical
text and all 77 numbered results and three definitions are unchanged from
v58. The reviewed v58 artifacts are retained. The Google report and its
assessment are in `docs/reviews/GOOGLE_V58_2026-11-14/`.

Theorem 5.3, Lemmas 8.9 and 9.6, and Corollaries 8.10 and 9.8 are complete.
The count is 74 proved results and three open: 10.7, 10.8 and 10.9. Proposition 10.7 is next. Preserve the
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
verification includes both complete axiom audits. Continue with Proposition
10.7: construct first-order fork syntax and parameterized finite derivations
for arbitrary nullary coefficients, including both atom-identifying transitions.

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
