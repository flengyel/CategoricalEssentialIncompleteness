# Syntax, derivations and soundness for the current manuscript

Continuation begun 5 November 2026.

The parameter-stable initiality results 5.5 and 5.8 remain proved. This
continuation completes the concrete named-variable substitution comparison
5.7, the categorical generated-theory assembly 5.9, semantic substitution
6.5, standard-code soundness 6.6 and its concrete arithmetic-ultrapower
transport 6.9. The uniform computation/production comparison 5.1 is also complete.
The categorical arithmetic application is tracked separately below; this is
not a claim that the whole current manuscript is formalized.

The active target is selected by `MANUSCRIPT_CURRENT.json`: currently version
47 at `manuscript/latex/main.tex`, with `FORMALIZATION_STATUS_V47.md`,
`CurrentStatementAudit` and `CurrentAxiomAudit`. `V46` module/namespace names and
this existing report filename are retained as implementation names. Future
manuscript revisions continue to follow the manifest.

The ongoing proofs started from verified main `fc47dd92e97373244f72bfe191456863e6de8e88`
and proof commit `5a361496f90f5bc20907182d35a883097959f63c`.
Origin main was integrated by fast-forward to
`0187c430832069adbd439e597225654ef10a7595`, including manuscript integration
`d3e741dc982a71f7f4678376eeffe945eb183d11`. All 245 then-modified/untracked
files were preserved and checked byte-for-byte; ignored continuation drafts
and failed logs remain preserved. Codex made no manuscript editorial changes.
The toolchain, dependency revisions and imported-source pins remain unchanged.

## Completed mathematics

Prefixes below abbreviate `CategoricalEssentialIncompleteness.V46`.
The manifest-selected current correspondence table gives the full
statements, effective hypotheses and separate application obligations.

| Result | Actual proved declarations and scope |
| --- | --- |
| 5.5, retained | `SyntacticSyntax.foldHom`, `foldHom_unique`, `withParametersInitial`, `postfixInitial`, `categoricalSyntax`, `plainCategoricalSyntax`, `totalCategoricalSyntax`, `plainTotalCategoricalSyntax`: constructor compatibility, uniqueness among all algebra morphisms and IsInitial in the base and every parameter slice. The same-word plain/stored parser comparison preserves constructors; the actual standard parser has its native primitive-recursive certificate. |
| 5.8, retained | `SyntacticDerivation.derivationAlgebra`, `derivationInitial`, `derivationFold_conclusion`, `derivationFold_constructor`, `derivationFold_unique` and their actual TotalSplit counterparts: arbitrary finite typed rule data, original premise pullbacks, nullary rules and the full slice universal property. |
| 5.7, canonical and plain comparison | `ConcreteNamedComparison.computedTerm_commutes`, `computedFormula_commutes`, `computedSubstitutionHom`, `computedStatePair_eq_fold` construct an actual substitution algebra morphism and use stable initiality. `plain_termSubstitution_value`, `plain_formulaSubstitutionOption_value`, `plain_formulaSubstitution_result`, `plain_admissible_model_iff`, `plainFreeForClassifier_isPullback`, `plainFreeForDomain_theory` identify the actual operations, success pullback and independent free-for predicate, including literal T-provable domain equivalence. |
| 5.7, genuine operation transport | `SyntaxOperationsTransport.substitutionAlgebraIso`, `substitutionFold_comparison`, `map_termSubstitution`, `map_formulaSubstitutionOption`, `mappedAdmissibleSubstitutionIso_inclusion`, `mappedAdmissibleSubstitutionIso_result` derive the diagrams through actual constructor, list, Boolean and option comparisons. `ConcreteSyntaxOperationsTransport.termSubstitution_comparison`, `formulaSubstitutionOption_comparison`, `admissibleIso_inclusion`, `admissibleIso_result` specialize them to the actual predicate/TotalSplit equivalence and mapped list record. Four raw concrete diagram checks are compiled. |
| 5.9 | `SyntacticGeneratedTheory` and `SyntacticGeneratedTheoryTotal` supply constructed initial proof algebras, formula-image closure and leastness, the sentence pullback and least sentence theory, and its selected-program/source restriction idempotent. `TotalSentenceImages` gives the actual inverse-chart literal Sent-and-program-range splitting. The completed 5.7 comparisons discharge the remaining operation-realization dependency. |
| 6.5 | `NamedPlainSemantics.evaluate_termSubstitution`, `holds_formulaSubstitution`: semantic substitution for the actual term morphism and the formula morphism on the constructed admissibility pullback, in arbitrary semantic K. No additional free-for or successful-output premise is supplied. |
| 6.6 | `NamedPlainSemantics.valid_logicalAxioms`, `valid_conclusion`, `valid_sentenceConclusion`, `soundnessFactor_inclusion`, `exists_unique_soundnessFactor`, `sentenceConclusion_range_consistent`: all seven actual schemes and both rules, induction on constructed standard derivations, the unique sentence-validity factor and disjointness with the actual negation preimage. The sole nonlogical hypothesis is validity of the actual sentence axioms in K. |
| Actual Γ filter | `NamedGammaSoundness.axioms_valid`, `exists_unique_factor` derive the soundness hypothesis and unique standard sentence-validity factor from satisfaction of enumerated literal named sentences in K, using the proved axiom formula-coordinate chart. No equality of chosen sentence codes with formula words is assumed. |
| Exact soundness data | `FirstOrderModelSoundness.axiomsProperty_iff`, `conclusionProperty_iff`, `sentenceProperty_iff` expose the complete raw model-graph conditions. `proofAlgebra_plain`, `sentenceProofObject_plain`, `conclusion_plain`, `sentenceConclusion_plain` prove literal equality to the existing generated-theory algebra, carrier and maps, including constructors. These wrappers do not assume initiality, evaluation or a soundness factor. |
| 6.9 | `NamedPlainSemantics.canonicalCodeComparison`, `canonicalSoundnessFactor_inclusion`, `canonicalValidity_disjoint`, `canonical_ultrapower_soundness`, `canonical_ultrapower_conclusion_consistent`: the actual proved standard factor is transported through realization and the constructed canonical arithmetic-ultrapower comparison. The comparison and factor are constructed, not application assumptions. |
| Finite derivation comparison | `SyntacticFiniteDerivations` realizes finite ordered original-rule trees in the actual proof carrier in every T-model. `SyntacticFiniteDerivationsStandard` proves the reverse conclusion comparison for N, with N models T explicit. `SyntacticNamedHilbert.Derives` is the separate literal named seven-scheme, axiom, generalization and ordered modus-ponens calculus; independent FreeFor and actual partial-substitution equations are retained. `SyntacticFiniteNamedDerivations.logical_scheme`, `nonlogical_axiom`, `generalization`, `modus_ponens`, `realizes` additionally realize the seven actual parameter families and both ordered rules in the constructed generated-proof object. Native literal-coordinate and older FFL/LK proof comparisons remain separate. |
| Arithmetic semantic comparison | `NamedArithmeticSignature` fixes the checked arithmetic coefficients. `ArithmeticNamedTranslation.translateTerm`, `translateTerm_freeVariables`, `evaluate_translateTerm`, `translateFormula`, `holds_translateFormula` preserve the explicit variable context and semantic interpretation in arbitrary arithmetic K. Target binders are named and fresh. This is semantic compatibility, not equality of syntax presentations or a derivability comparison. |
| Literal proof support | `NamedHilbertPropositional.deduction`, `doubleNegElim`, `doubleNegIntro`, `conjunction_intro`, `disjunction_elim`, `systemClassical`, `system_provable_iff`: actual literal-calculus proofs and a constructed classical propositional entailment instance, for arbitrary coefficients and Γ. Local hypotheses have propositional inference only. This supplies logical support, not a first-order proof-presentation comparison. |
| Actual Γ theorem image | `SyntacticGeneratedAxioms.theoremCarrier_model`, `literalTheoremCarrier_model`, `axiomProof_conclusion`, `axiomProof_value`, `theoremProgram_theory`: actual constructed Γ proof/conclusion/image and selected literal source-program predicate, in every T-model and as a literal T-provable sentence. The external native/FFL derivability comparison remains separate. |
| Numerical source object | `ArithmeticOmegaComparison.variables_idempotent`, `omegaIso` prove that the literal all-variable realization is the actual identity splitting of ω, for every T extending PA, by universal T-model graph equality. |
| Native point adapters | `SyntacticNamedHilbertCoordinates` proves actual named constructor point equations, independent named free-for to the genuine admissibility pullback, and the actual categorical output of successful native substitution. Its standard code interpretation is explicitly PA/N. The full native finite-proof realization is still a draft. |
| Model computation dependencies | `NamedArithmeticStandardCodes` proves positive standard-code transfer. `NamedArithmeticModelCoding`, `ModelSubstitution`, `ModelOccurrences` prove finite constructor charts and actual reconstruction/FV equations with arbitrary internal child values and typed closed replacements in every PA model. The equal binder returns the original whole quantified word. The remaining combined FV-bound/sentence-range/Pred Θ draft timed out at its 40-second diagnostic cap and is unclaimed. |
| Actual sentence chart | `SyntacticSentenceLiteralChart.toSentenceIso`, `toSentence_over`, `toSentence_value`: the literal sentence predicate is isomorphic to the actual chosen sentence object, with its inclusion triangle and formula-coordinate value proved for every T-model, arbitrary T extending PA and arbitrary coefficients. |
| Arithmetic source diagonal component | `ArithmeticDiagonalCodes.diagonalIndex_represents`, `sourceTau_isTuring`, `source_pair_inseparable`, `model_a0`, `model_a1`, `printed_tau_is_universal`, `printed_parity_is_identity`: actual printed-u source morphisms, a PA-total adapter with proved factorization, exact diagonal source equality, PA disjointness and all-PA-model restriction-domain comparisons. This proves a component of 7.1, not its Γ inequalities. |
| Arithmetic numeral dependency | `NamedArithmeticNumerals` proves the actual internal numeral graph, zero/successor equations and native primitive-recursive certificate. `NamedArithmeticNumeralCarriers.numeralCode_carrier_closed`, `numeralCode_closed` prove accepted term membership and numerical FV=0 for every internal input in every PA model, including nonstandard inputs. `NamedArithmeticNumerals.numeralMorphism` is the actual PA-total graph into closed terms; `numeralCode_standard` proves its exact standard external word. `translateFormula_freeVariables` and its unary specialization prove the external formula FV bound. `NamedArithmeticClosedSubstitution.substitutionFreeFor_closed`, `substitutionResult_closed`, `closedReplacement_PA` prove independent free-for and typed option success for every internal typed formula and typed FV-zero replacement, for arbitrary coefficients in every PA model. The fixed-formula sentence-range obligation remains separate until checked. |

Initiality assumes only T extending PA, with arbitrary coefficient predicates,
arity bounds, parameters, target families and actual algebra operations proved
supported and total in T. Target operations need not be primitive recursive
or PA-provably total. No consistency, c.e., soundness or standardness hypothesis
on T is added. Carrier-membership, evaluation and conclusion witnesses remain
existential witnesses rather than extra syntax labels.

The manuscript polynomial and named variables are unchanged. Derivation
constructors use the original `R_n ×_(F^n) Z^n`; each child matches its own
prescribed premise and the parent conclusion is induced by `q_n`. Nullary
rules require no global point of the formula object.

The equal-binder substitution branch retains the original body even when
recursive substitution fails. Free-for is the independently defined recursion,
not a definition in terms of result tags. The actual formula-coordinate
sentence image is T-provably plain Fm with FV=0. A chosen pullback object's raw
code is not identified with the formula code, and arbitrary inverse-equivalence
charts are not asserted to be primitive recursive.

Standard decoding and finite-tree reverse comparisons concern N. They do not
identify nonstandard words with external finite trees or assume preservation
of initiality by a Set model functor. Semantic K is distinct from code models
N and M; validity-negation disjointness requires nonempty K. The 6.9 instance
uses the actual realization of the constructed predicate proof/conclusion data
and the canonical arithmetic-ultrapower interpretation.

## Uniform computation comparison

Exponential/parity object coding is complete and is separate from the uniform
trace bridge. The actual trace predicate/output reader, native certificates,
PA functionality/universal equation, and internal history-prefix/lookup laws
are proved. `UniformTrace.specialization_PA`, `composition_PA` and
`builders_totality_PA` prove the uniform graph equations and uniquely total
index-builder graphs for arbitrary internal indices and parameters in every
PA model. `specialize_primrec`, `compose_primrec`, `specialize_natPrimrec` and
`compose_natPrimrec` certify the actual standard functions.

`specializerSectionIndex`, `specializerSection_eval` and the section-program PA
graph/totality sentences supply the actual fixed-e program k_e on all internal
inputs. `compose_production_PA` proves that the actual new and canonical production
composition indices have equal graphs in every PA model on all internal
inputs, for fixed external indices. `arithmetized_evaluation` assembles the
closed concrete principal result. All section/comparison/principal source and
raw statement-check files passed production builds and strict replays; no
trace obligation remains in this assigned Lemma 5.1 scope. No arbitrary-internal-index stage-persistence assumption is used.

## Verification and source identity

The preceding complete run is preserved at
`.codex-work/verify-20261105T125741Z-QgX9an`: 510 successful commands,
1,274 retained and 7,652 v46 declarations, 259 production modules, 763 inputs,
and snapshot SHA-256
`d6d693bd3c75d1b542926990fb4984e547f59fd8bf6381593cbd46f314849a54`.
Those tested proof inputs matched the preceding committed checkpoint before
implementation, except for the subsequently extended combined import lists.
That historical baseline was reused for unchanged proof sources; it is not a
full verification of the later manuscript target. The original reviewed 516-input/263-command baseline
and hash `9c92ef0cf86c226adbb3a8ddd03fa1d74eb056e245cb3f3adaf7ac2037f8a2d9`
remain in the previous committed verification records.

The required current-manuscript v47 `bash scripts/verify-wsl.sh` passed with exit **0** under the
existing lock and `LEAN_NUM_THREADS=1`. Run: `.codex-work/verify-20261106T000653Z-wVCQvv`.
All 783 commands passed: combined build, both statement audits,
every strict source/check replay and transitive axioms. The audit retains
all 1,274 earlier declarations and covers 10,610 current-production declarations in
406 production modules. Its axiom union is exactly `propext`, `Quot.sound`,
`Classical.choice`. All 16 dependencies were clean and pinned at start/end;
356 imported-source pins and 25 current manuscript files and artifacts passed.
All 1065 tested inputs match committed bytes at proof commit
`670c6b04d5bd9f661c0019d7b4e8dcb782f6168d`, whose ordinary main push and remote ref were confirmed.
Source-snapshot SHA-256: `0b6c1df38427b837b9998f08335ea8e2bcf1ef863170bfea1959b09ba191b019`.
The separate report commit and Downloads copies are checked by the existing
committed-byte delivery procedure.

Lean remains `v4.35.0-rc2`, compiler
`11acb17ec6b07a8f9e9173e6845197929540936b`; Mathlib remains
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; Foundation remains
`01f617fbe240a84aaf1c45b31b9d65e0a2e21c1d`.
The existing verifier checks all 16 dependency worktrees before and after the
build, preserving and reporting changes. The current manuscript-only gate
passed after main integration. The preceding v46 full replay was deliberately
interrupted with observed exit 130 to integrate the current target; its partial
logs are retained and no full pass is inferred. The manuscript chat supplied
no full v47 Lean pass either.
The existing report, verification JSON, source manifest and Downloads delivery
procedure are reused.

The independent review of `3f53b33` inspected source and recorded verification
evidence. It did not independently rerun Lean or establish completion of v46,
and found no confirmed mathematical drift in that snapshot. It correctly
distinguished evaluator uniqueness from algebra initiality, arbitrary-rule
initiality from a particular calculus, object coding from uniform trace
comparison, and arithmetic incompleteness from its required categorical
application. New source/type reviews and kernel runs here are author-side or
collaborating-agent work, not an independent whole-paper certification.

## Remaining mathematical dependencies

The completed uniform trace comparison remains separate from the completed
exponential/parity object coding. Neither is used as a substitute for the
arithmetic application below.

Sections 7.1–7.3 still require the actual arithmetic Gamma theorem/refutation
predicate identifications, a PA-total fixed-formula sentence map,
the specified diagonal bounds for every M elementarily equivalent to N, the
actual partial proof-search instance and the categorical comparison application.
Native-to-actual proof charts and the particular older FFL/LK derivability
comparison remain distinct proof obligations. The checked semantic translation
does not supply derivability.
The arithmetic source diagonal now uses the actual printed universal map.
Its Turing property is proved through a PA-total source adapter and an actual
factorization equation with the older typed Turing morphism. The two morphisms
are not identified. The diagonal index and all-model partial-identity comparisons
are proved; Γ inequalities remain separate.

Our checked numeral convention uses zero followed by add(previous,one), so
numeral1 is zero+one. Foundation's canonical numeral1 is the one symbol. Their
semantic agreement is not literal constructor equality. A later proof transfer
must use an explicitly translated zero/add-one chain or prove the required
numeral/substitution/derivability comparison.

External consistency of Gamma is not a PA proof of its consistency. Fixed
standard parameter-free graph comparisons do not automatically cover arbitrary
nonstandard indices or model parameters. The proof-search lift remains partial;
a complementary total switch or an imported arithmetic incompleteness theorem
does not replace the categorical application.

Indexed families, numerical inference realization, Miller representation
independence and cosheaf derivation initiality remain later obligations. Rows
9.1 and B.10 retain the corrected status of the completed numerical tuple
comparison in 7.7. Manuscript editing belongs to the manuscript chat; this proof batch preserves its integrated target.
