# Proposition 10.7: first-order fork realization complete

Proposition 10.7 is proved. The completed first-order syntax now has
initial finite derivation algebras for all seven logical schemes and both
inference rules, for arbitrary nullary coefficient diagrams and axiom
subobjects in every parameter slice. Natural evaluation, the full
constructor equation and uniqueness include every target family and all
underlying natural algebra morphisms.

The count is **75 of 77 numbered results proved**. Proposition 10.8 and
Corollary 10.9 remain open. Manuscript v59 and its source, PDF, archive
and manifest are unchanged. This batch completes the remaining derivation
clause; the [full syntax batch](V59_FULL_FORK_SYNTAX_2026-11-16.md) supplies
the canonical term/formula algebra, parameter stability, stable variable
lists, occurrences, admissible substitution and sentence objects.

## Construction

`ForwardRuleRelabelling` uses the existing `RulePresentation.Translation`
type and its premise-input construction. It proves the forward inference
comparison, composition and raw fold uniqueness along arbitrary formula
and rule-label morphisms. The original isomorphism-based
`V46RuleRelabelling` module is retained verbatim. There is no injectivity
or equality-reflection hypothesis on atom relabelling.

`FiniteInferenceEvaluation` compares the entire inference endofunctor:
ordered finite powers, rule-input pullbacks and finite coproducts. It
proves the comparison squares under arbitrary natural transformations.
Naturality of each global algebra operation supplies its actual component
constructor square, rather than a new compatibility assumption.

`InitialRuleDiagrams` defines proof transitions by the initial component
folds, proves their identity and composition laws, and assembles the
global carrier and constructor. The actual evaluated source is compared
with every component source by an algebra isomorphism. Folds into any
global target are natural and satisfy the constructor and conclusion
equations. Uniqueness covers all underlying natural morphisms satisfying
those equations.

`NumericalDiagramDerivations` supplies the component initial algebras from
the existing numerical finite-tree construction. Its equation-controlled
guard retains that exact source; local initiality is discharged, not
assumed in the final result. The iterated-slice equivalence transports
the complete inference functor and initiality to arbitrary parameter
slices, including nonconstant formula and target families.

`ForkParameterizedDeduction` instantiates the actual seven scheme objects,
including admissible-substitution and absence side conditions, together
with generalization and ordered modus ponens. It constructs
`NullaryPresentations numbers`, relative initial proof algebras and the
printed inference algebras over P × Fm. Their ordered-premise comparison
retains the same parameter in each child and its conclusion. The
`printedStatement` construction has no evaluator, initiality, preservation
or transition-compatibility hypothesis.

The required proof families are indexed only by axiom subobjects.
`presentationGeneration_obj` is generation from the regular image of an
arbitrary axiom morphism; it uses only those subobject-indexed proof
families. The construction never needs a global formula-equality test:
atom transitions preserve successful premise matches and may identify
labels. The Boolean truth/success and quantifier conventions are retained.

Independent `V46ForkParameterizedDeductionChecks` restates the complete
printed scope. It checks syntax/list parameter stability, full numerical
variables and the variable/term isomorphism, the true injection, sentence
and admissibility pullbacks, occurrence/substitution naturality, all seven
scheme objects, both rules, arbitrary parameter-dependent axiom subobjects,
every target algebra, the conclusion and constructor equations, raw
uniqueness and naturality. It also checks the actual source/component
algebra isomorphism and regular-image presentation generation.

## Verification

Proof commit: `a575d8d8b6660628886d6a59c2f556ea211d75ba`.
All **18 successful incremental commands** passed, including **10 strict
elaborations**, the project build, both statement audits, parser tests,
the manuscript gate and both complete transitive axiom audits. The
current audit covers **1,042 production
modules** and **31,174 declarations**; the
retained audit covers **1,274 declarations**.
The independent Checks module has **37 principal axiom reports**. All
principal reports and both complete audits use only `propext`, `Quot.sound`
and `Classical.choice`.

All sixteen dependency worktrees remained clean and pinned, and
356 provenance pins passed. All
**2,571 measured inputs** remained unchanged and
matched the proof commit. The measured delta is eleven files: five new
producers, one Checks module, four production/audit entry points and the
correspondence table. No prior production proof or dependency was changed.
Previous inputs were matched to their published proof commit.

The six selected producer/Checks sources also passed separate targeted
strict checks at 2 GB with a 120-second command limit. Integrated strict
checks used 3 GB and explicit command limits. Runs used the serial build
lock and one Lean thread. The initial complete current audit reached its
600-second shell limit (exit 124). Its failed record and logs are retained
at `.codex-work/v59-fork-derivations-20261116/incremental-verification/`.
The seventeen successful commands were reused only after their log hashes,
the complete source snapshot, proof commit and dependency state were
rechecked. Only the failed audit was rerun, with a 900-second limit and
the same 3 GB cap. The final record contains eighteen successful commands
across these attempts; the timed-out audit is excluded from that count. The historical WSL recovery
archive and reviewed v58 artifacts are retained verbatim.

The [machine-readable record](V59_FORK_PARAMETERIZED_DEDUCTION_VERIFICATION_2026-11-17.json) contains command and source hashes,
module coverage, principal reports and targeted results. Raw record:
`.codex-work/v59-fork-derivations-20261116/incremental-verification-final/verification.json`;
SHA-256 `e069e6dfd4a6c3cbc89e67a9db6d1dfc8791fa273e969a292df8829b32f5d89b`.

This is completed **incremental verification**, including the complete
proof of Proposition 10.7. No new full replay was run. The last completed
[full v59 replay](V59_FULL_VERIFICATION_2026-11-14.md) remains the
1,798-command run at `8df18834734179186459d3c4c34d4c0cf20b6194`.

## Resume point

Continue Proposition 10.8 using the actual coefficient diagram V from
the completed propositional fork. Construct the natural propositional
embedding and erasure, retaining the existing total-category and
numerical-code comparisons. Erasure sends equality to the printed global
propositional tautology and universal quantification to the second
projection. Prove erasure invariance under admissible substitution, the
logical-scheme and inference-rule comparisons, conservativity and
consistency of the generated first-order theory. Then prove internal
essential incompleteness and the selected-endpoint conclusions for every
consistent c.e.-axiomatized first-order extension.

For Corollary 10.9, apply the completed Theorems 5.2–5.3 with the now
constructed all-parameter deduction and the common global logical theorem.
Retain arbitrary closed consistent extensions, including nonconstant
slice families. Use the original inseparable atom generators and
restriction/category comparisons. Do not add preservation or
incompleteness conclusions as hypotheses. Keep v59 unchanged unless an
actual mathematical defect is established.
