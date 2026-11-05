# Syntax and derivation continuation — 2026-11-05 (UTC)

Proposition 5.5's parameter-stable syntax initiality and Lemma 5.8's
arbitrary-rule derivation initiality remain proved in the predicate category
and actual total restriction splitting. The present batch continues their
logical realization: numerical substitution and free variables, the actual
categorical occurrence fold and sentence predicate, standard named-code
comparisons, generated-theory assembly, standard derivation induction and
initial soundness results. The remaining categorical substitution/admissibility
comparison, complete coded soundness and arithmetic application are explicit
open obligations.

This is the existing implementation record, continued from proof commit
`54a5905ac392469b5e78ec1232a64952d85df942` and report commit
`4cde20bb86edd9878336eb74a09f1cc6dc61e8af`. Earlier committed records, ignored
continuation drafts and failed-elaboration logs are preserved. The manuscript
entry remains `manuscript/latex/main.tex`, version 46; no manuscript prose,
theorem statement, toolchain, dependency revision or imported-source pin changed.

## Completed mathematics

Declaration prefixes below abbreviate `CategoricalEssentialIncompleteness.V46`.
The rows distinguish completed results from proved dependencies of an unfinished
numbered result.

| Result or dependency | Proved declarations and exact scope |
| --- | --- |
| Proposition 5.5, retained complete result | `SyntacticSyntax.foldHom`, `foldHom_unique`, `withParametersInitial`, `postfixInitial`, `categoricalSyntax`, `totalCategoricalSyntax`, `plainCategoricalSyntax`, `plainTotalCategoricalSyntax`: actual constructor commutation and uniqueness among all algebra morphisms, in the base and every parameter slice. The plain parser/stored-word comparison preserves the same numerical word and constructors; `NatVectors.run_natPrimrec` supplies the actual standard parser certificate. |
| Lemma 5.8, retained complete result | `SyntacticDerivation.derivationCarrier`, `derivationConclusion`, `derivationAlgebra`, `derivationInitial`, `derivationConstructor_tree`, the fold conclusion/constructor/uniqueness laws and all `totalDerivation*` counterparts: the initial algebra for arbitrary finite rule data, original premise pullbacks, arbitrary coefficient predicates and nullary rules. |
| Numerical part of 5.7 | `ConcreteNamedSubstitution.freeVariables_carrier`, the guarded term/formula constructor equations and `freeVariables_natPrimrec`; `substitutionPayloadGraph_eval`, `substitutionResultGraph_eval`, `codedSubstitutionPayload_natPrimrec`, `codedSubstitutionResult_natPrimrec`, `substitutionPayload_carrier`, `substitutionResult_term`, `substitutionResult_formula`, `substitutionFreeFor_iff_success`, `substitutionPayload_term_constructor`, `substitutionPayload_formula_constructor`: actual total numerical traversals, primitive-recursive certificates and typed constructor laws in every PA model. `substitution_total_PA`, `substitution_preservation_PA`, `freeVariables_preservation_PA` and `freeFor_success_PA` export explicit PA proofs. |
| Actual list and FV fold comparisons | `ConcreteNamedComparison.appendParameter_eq`, `membershipArrow_eq`, `deletionArrow_eq`, `occurrenceHom`, `plainOccurrenceHom`, `plain_termOccurrences_eq`, `plain_formulaOccurrences_eq` and their all-model values: the numerical operations agree with the specified categorical folds. The occurrence comparison is a proved algebra morphism and uses initiality; evaluator uniqueness alone is not substituted for that argument. The literal occurrence-graph equality is also proved in PA. |
| Intended sentence codes | `ConcreteNamedComparison.literalSentenceCarrier`, `sentenceCarrier_literal`, `sentenceCarrier_literal_theory`: the formula-coordinate image of the actual sentence inclusion is T-provably exactly plain formula acceptance together with numerical FV=0. The chosen pullback object's own code is not assumed to be the formula code. |
| Standard named syntax and operations | `NamedPostfixEncoding.termEquiv`, `formulaEquiv`; `NamedPostfixPlainComparison.plainTermModelEquiv`, `plainFormulaModelEquiv`: bijections with the actual standard accepted/plain categorical carriers. `freeVariables_termCode`, `freeVariables_formulaCode`, `substitutionResult_termCode`, `substitutionResult_formulaCode`, `substitutionFreeFor_formulaCode`: the actual numerical algorithms compute literal named substitution and the independently defined recursive FreeFor condition. Names, labels, arity tags, repetitions in occurrence lists and ordered children are retained. |
| Actual constructor values and Boolean reflection | `NamedPlainConstructorModels.plainTerm_value`, `plainFormula_value`; `NamedPlainOperationsModels.variable_value`, `equality_value`, `negation_value`, `implication_value`, `quantifier_value`: values of the actual plain categorical constructors at arbitrary T-model inputs. `ConcreteNamedComparison.membershipArrow_point_iff` uses the actual Boolean isomorphism to reflect the numerical membership flag. No inverse for a general polynomial encoder or arbitrary chosen coproduct-code identity is assumed. |
| Structural assembly of 5.9 | `SyntacticGeneratedTheory.proofInitial`, `generated_theory`, `sentence_theory_pullback`, `sentence_axioms_factor`, `sentence_theory_closed`, `sentence_theory_least`, `sentence_theory_idempotent`, `sentenceConclusion_range`, `literalSentenceRestrictionSplitting`, and the actual TotalSplit counterparts: constructed derivations supply formula-image closure/leastness, the sentence pullback and generated sentence theory, and its representing program-range/source idempotent. Full numerical realization still depends on the remaining 5.7 comparisons. |
| Standard derivation induction | `SyntacticDerivation.StandardInduction.typed_children_smaller`, `derivation_constructor_cases`, `nat_rule_induction`: induction on the actual standard derivation carrier, with each original typed child separately bounded by the parent node count. Finite coproduct preservation and the constructed initial algebra's structure isomorphism give constructor cases; preservation of initiality in Set is not assumed. |
| Proved coded semantic dependencies of 6.6 | `NamedPlainSemantics.decodeTerm`, `decodeFormula`, constructor decoding and semantic laws, `valid_hilbertOne`, `valid_hilbertTwo`, `valid_hilbertThree`, `valid_hilbertReflexivity`, `valid_generalization`, `valid_modusPonens`, `valid_negation_disjoint`: four actual standard coded schemes, both rules and formula-level validity-negation disjointness. The semantic structure K is separate from the arithmetic code model. Distribution, instantiation, equality substitution and the actual derivation validity factorization remain open. |
| Completed trace predicate fragment of 5.1 | `UniformTrace.trace_primrec`, `traceCheck_natPrimrec`, `PrimitiveCoding.PrimitiveTotal.traceProgram`, `primitive_trace_graph_PA`, `traceProgram_comparison_PA`: the actual trace predicate is primitive recursive, with its PA defining-program graph comparison. `ModelHistory.history_nth_stable`, `lookup_history_eq`, `prefix_lookup_iff` prove the actual internal history/lookup comparison for arbitrary model stages, indices and inputs. Uniform composition/specialization and PA-total parameter-index programs remain open. |
| Transport dependencies | `SyntaxOperationsTransport.mapped_fold`, `mapped_fold_comparison`, `plain_mapped_fold` and coefficient-expression equations: genuine fold equalities through the actual polynomial/algebra comparisons and counit components. They are a transport resource, not a claim that all TotalSplit substitution, list, Boolean and option-operation comparisons are finished. |

The syntax and derivation universal properties assume only T extending PA.
Coefficient objects, arity bounds, parameters, target families and actual
T-supported total algebra operations are arbitrary. Those operations need
not be primitive recursive or PA-provably total. Consistency, c.e., soundness
and standardness of T are not hypotheses of initiality.

The manuscript polynomial is unchanged:
`K(X,Y) = (V + sum Sigma_k × X^k,
X^2 + sum Pi_k × X^k + Y + Y^2 + V × Y)`.
Carrier-membership, computation and conclusion witnesses are existential,
not extra syntax labels. Derivation constructors use the original
`R_n ×_(F^n) Z^n`; each child matches its own prescribed premise, and the
parent conclusion comes from `q_n`. Nullary rules need no global formula point.

The numerical algorithms have separate PA-level proofs and standard
primitive-recursive certificates. Their equal-binder substitution branch
retains the original body even when recursive substitution fails. Its
standard comparison proves this behavior without changing the algorithm or
defining free-for to mean successful substitution.

The standard-tree comparisons concern N. They do not identify nonstandard
words with external finite trees or assert Set initiality for all functions
in nonstandard models. The general standard-induction helper explicitly
assumes N models T; the soundness application uses T=PA. K interprets decoded
formulas and may have any universe; validity-negation disjointness requires
nonempty K.

## Verification and source identity

The preceding complete verification is preserved at
`.codex-work/verify-20261105T082552Z-2Hh2l8`: 386 successful commands,
1,274 retained and 6,143 v46 declarations, 197 production modules and 639 inputs.
Its snapshot hash is
`f27917912324e1441cf25533a3307d39a3d16a29eb66ccd6910b707b412487a4`.
All 639 inputs match report commit `4cde20bb86ed`, so that baseline was reused.
The original reviewed 516-input baseline and its
`9c92ef0cf86c226adbb3a8ddd03fa1d74eb056e245cb3f3adaf7ac2037f8a2d9`
hash remain in the previous committed verification record.

The current preflight has 763 inputs: 124 new Lean source/check files and two
changed previous inputs, the combined entry and statement-audit import lists.
Every new file is directly imported. All previous proof sources, 356 imported
pins, the pinned toolchain, all 16 dependency revisions and manuscript v46
remain unchanged. All dependency worktrees were clean and pinned at preflight;
the existing verifier also checks them before building and after the axiom audit.

The required `bash scripts/verify-wsl.sh` passed with exit **0** under the
existing lock and `LEAN_NUM_THREADS=1`. Run: `.codex-work/verify-20261105T125741Z-QgX9an`.
All 510 commands passed: combined build, both statement audits,
every strict source/check replay and transitive axioms. The audit retains
all 1,274 earlier declarations and covers 7,652 v46 declarations in
259 production modules. Its axiom union is exactly `propext`, `Quot.sound`,
`Classical.choice`. All 16 dependencies were clean and pinned at start/end;
356 imported-source pins and 24 v46 manuscript files passed.
All 763 tested inputs match committed bytes at proof commit
`5a361496f90f5bc20907182d35a883097959f63c`, whose ordinary main push and remote ref were confirmed.
Source-snapshot SHA-256:
`d6d693bd3c75d1b542926990fb4984e547f59fd8bf6381593cbd46f314849a54`. The separate report commit and Downloads
copies are checked by the existing committed-byte delivery procedure.

The first integration attempt,
`.codex-work/verify-20261105T125509Z-nDj91A`, found that 19 new entry imports
followed the existing module documentation command. Moving them into the
initial import block fixed that packaging error; no proof body, theorem
statement or Lean limit changed. The failed log and snapshot are preserved.

Lean remains `v4.35.0-rc2`, compiler
`11acb17ec6b07a8f9e9173e6845197929540936b`; Mathlib remains
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; Foundation remains
`01f617fbe240a84aaf1c45b31b9d65e0a2e21c1d`.
The [verification record](V46_SYNTAX_CONTINUATION_VERIFICATION_2026-11-05.json),
[source manifest](reviews/V46_SYNTAX_CONTINUATION_SOURCE_SHA256_2026-11-05.txt),
[scoped review](reviews/V46_SYNTAX_CONTINUATION_REVIEW_2026-11-05.md) and
[writing review](reviews/V46_SYNTAX_CONTINUATION_WRITING_2026-11-05.md) use the
existing report/delivery procedure.

The independent review of `3f53b33` inspected source and recorded evidence;
it did not independently rerun Lean or certify completion of v46. It found
no confirmed mathematical drift in that snapshot. New source/type reviews
and kernel checks here are author-side/collaborating-agent work.

## Remaining mathematical dependencies

Lemma 5.1 still requires uniform composition and specialization equations for
arbitrary internal indices/parameters, PA-provably total parameter-index
programs and their production graph/index comparison. The trace predicate's
primitive-recursive certificate and PA defining-graph comparison are now
proved. Completed exponential/parity object coding is a separate result.

Proposition 5.7 still requires the actual categorical substitution algebra
morphism and stable-initiality comparison, its success pullback/free-for
identification and genuine operation transport through the chosen TotalSplit
comparisons. Numerical algorithms, standard named comparisons, categorical
FV and the literal predicate-category sentence identification are proved.
Theorem 5.9's structural construction is proved; its complete numerical
realization retains those remaining operation comparisons.

Lemma 6.5 requires applying the proved numerical/named substitution comparison
to the actual categorical admissibility domain. Proposition 6.6 requires the
remaining three actual scheme validities, soundness of constructed coded
derivations, the unique sentence validity factorization and disjointness with the actual sentence-negation preimage.
Only that proved factorization can instantiate the arithmetic-ultrapower
transport in 6.9.

Sections 7.1–7.3 still require the actual Gamma theorem/refutation predicates,
diagonal bounds, partial proof-search lift and categorical comparison
application. Importing an arithmetic incompleteness theorem does not replace
that application. External consistency of Gamma is not a PA proof of its
consistency. Retain the required model scope, including M elementarily
equivalent to N where specified, arbitrary nonstandard inputs and model
parameters. The proof-search lift remains partial.

Indexed families, numerical inference realization, Miller representation
independence and cosheaf derivation initiality remain later obligations.
Rows 9.1 and B.10 retain the corrected wording about the already-proved
numerical tuple comparison in 7.7. Manuscript prose revisions remain deferred.
