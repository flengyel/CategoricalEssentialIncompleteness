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
48 at `manuscript/latex/main.tex`, with `FORMALIZATION_STATUS_V48.md`,
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

The arithmetic continuation resumes from verified main
`eff88a8bdefbc206b6231037b546bc8af8055fcc` and proof commit
`670c6b04d5bd9f661c0019d7b4e8dcb782f6168d`. All 1,065 verification inputs
matched that completed checkpoint before this batch. The completed syntax,
derivation, trace, substitution and soundness proofs are reused. The new work
constructs the fixed-formula and diagonal sentence morphisms, identifies the
actual Gamma refutation image, and realizes arithmetic proof search at the
actual generated theorem/refutation predicates.

The 6 November arithmetic application resumes from main
`0c44cdafed271546347dc5ba3191987eb9a155fb` and proof commit
`16ec62198d0aaa6506fc50d949f35af0fb26d94d`. All 1,119 inputs matched
that successful 837-command checkpoint before changes began. The concrete
Γ/PA axiom comparison, both printed bounds of 7.1 and all conclusions of
the categorical application 7.3 were proved by the subsequent 905-command
core batch. That batch also constructed the indexed axiom/rule family and
its initial algebra; numeral-fiber initiality and the uniform sentence
morphism remained open at that core checkpoint.

The indexed continuation starts from main/report commit `1db7a66` and proof
commit `e08d21c7eee33e6e7ee398411124039133a92905`. All 1,187 tested inputs
matched that completed 905-command checkpoint. The present proof batch
completes 7.5 and 7.6: the actual numeral-fiber universal property and
sentence pullback, the printed exponential axiom/proof presentations, their
PA-provable numeral-fiber comparison, the chosen PA-axiom enumeration and
one total sentence morphism with the stated standard-fiber independence.
Targeted builds, strict statement checks and the integrated full
verification passed, as recorded below.

The numerical continuation integrates main `2e7152b`, the v48 abstract
revision, from the verified v47 checkpoint `c51c34d`. All earlier Lean
inputs match the 965-command run at proof commit `ff0363b`; the active
manuscript metadata, abstract and artifacts have advanced to v48. The
v48 manuscript-only gate passes. No mathematical manuscript source has
changed in this Lean batch.

The constructed numerical syntax is initial in every parameter slice,
and the constructed successful finite-rule word algebra is initial for
every finite rule presentation, including nullary rules and empty
coefficients. The tuple-coordinate isomorphisms, generated-theory images,
literal syntax algebra comparisons and arithmetic graph transport have
passed focused production builds and strict statement checks. Native term
and formula decoding, the literal full Option-valued substitution and
independent free-for values, the sentence-membership comparison, and the
literal list support/nil/cons values are also checked. The actual unary
word-carrier syntax algebra and list algebra have constructor-preserving
isomorphisms and proved initiality in every required parameter slice.
The exact polynomial
input-code comparison and the original-rule validator comparison are proved;
the latter covers both success and failure for arbitrary finite PA rule
signatures. Formula-coordinate changes preserve the original proof word in
both directions. Arbitrary coefficient-rule isomorphisms have inverse
computable relabelling folds, both constructor/conclusion equations,
ordered-child and label equations, and uniqueness among all algebra
morphisms. These are supplied by the constructed inference initial algebras.
The actual arithmetic syntax now has the proved negation diagrams and a
numeral-substitution sentence morphism with the exact native zero/add-one
output and canonical standard PA value. These are
`NumericalArithmetic.SentenceMorphisms.negation_square`,
`standard_literal_result` and `theta_standard_interpretation`. The full
PA-to-numerical derivation-algebra transfer has since passed targeted
production and expanded statement checks: `interpretationAlgebraIso`
preserves the actual inference constructors, `interpretationCodeIso` has
both conclusion equations, and `mappedDerivationInitial` supplies folds
and uniqueness among all algebra morphisms for arbitrary finite PA rule
presentations. The used coefficient casts agree with the original
interpreted rule coproduct. The same isomorphism preserves the original proof word in both
directions; its exact dimension-one coding equations pass expanded checks.
The actual arithmetic term/formula constructor diagrams, substitution
domains and results, and unary/binary ordered rule-label comparisons also
pass production and expanded statement checks. All nullary scheme/Γ labels
and the concrete inverse proof relabellings now have checked premise/conclusion and constructor/label/ordered-child
equations. The final exact PA sentence-proof comparison, canonical standard-domain
isomorphism and both computable directions are proved. The actual numerical
regular image is the fixed Prov_Γ predicate, without a representation or
proof-translation premise. The unnumbered 08d argument applies Corollary 4.3
to these actual numerical theory objects. The printed PA-axiom inclusion gives the actual
finite-proof extension and third bound; the standard diagonal comparisons
give the other two bounds. External consistency gives disjointness.
`NumericalArithmetic.Incompleteness.categorical_incompleteness` and
`syntax_categorical_incompleteness` prove inseparability and noncoverage
on the literal sentence object and the constructed syntax sentence object
through the proved chart. Proposition 7.8 and the actual numerical
application are complete in this integrated, fully verified proof batch.
The integrated full verification below covers these completed
comparisons and the actual numerical application. The preceding v47
result and earlier v48 syntax checkpoint remain historical evidence.

The cosheaf continuation starts from verified main/report commit
`e5a95a4252edd1dceb6db997e4fa79b6098a9322` and numerical proof commit
`bcf6db5127e8507d1cbfe7975879a2f97fb9a7b2`. All 1,431 inputs matched
that completed 1,149-command checkpoint. The new batch proves Proposition
9.3's actual initial-H presentation, identifies its conclusion image and
endpoint theories in 9.4, and discharges the presentation comparison for
9.6. It preserves the original finite-proof carrier and conclusion.

Here S is the formula object, A and B are the two atomic axiom domains,
Ax=S²+S³+S²+A+B, and M(Q,q) is the ordered modus-ponens premise pullback
for q:Q→S.

For every target slice algebra, the constructed fold is natural and total
on its supported carrier, commutes with every constructor, and is unique
among all algebra morphisms. The component construction evaluates the
selected supported tree. It does not demand globally total ambient
operations or a decidable or inhabited coefficient carrier. The literal
WalkingSpan diagram in numerical tuples has the proved finite-power,
ordered-premise, rule-label, constructor and five-summand axiom comparisons.
The constructed initial conclusion image is the earlier t0, including its
actual inclusion, leastness, atomic bounds and consistency under disjointness.
Arbitrary c.e. axioms in either selected endpoint language are covered
without a compatible family of extensions.

All 13 producer/check pairs passed 52 production commands and 26 separate
strict scratch-source checks before the combined statement and automatic
axiom audits. Failed elaborations, timeouts and diagnostic snapshots remain
preserved separately. Removing unused generated reassociation attributes,
using generic categorical equations, and splitting large modules at actual
proof boundaries resolved the measured elaboration costs. The development
runner's per-command wall-time limit changed from 25 to 45 seconds; Lean
heartbeat limits, the kernel,
toolchain, dependency pins and mathematical hypotheses were unchanged.
The user stopped a separate verification before the final targeted replay;
its contribution to earlier timing problems is not established.

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
| Native point adapters | `SyntacticNamedHilbertCoordinates` proves the named constructor point equations, independent named free-for to the genuine admissibility pullback, and the categorical output of successful native substitution. Its standard code interpretation is PA/N. The subsequent `SyntacticNamedHilbert.native_realizes`, `native_sentence_theorem` and `native_sentence_refutation` now realize finite native proofs in the constructed Γ derivation carrier. |
| Model computation dependencies | `NamedArithmeticStandardCodes` proves positive standard-code transfer. `NamedArithmeticModelCoding`, `ModelSubstitution`, `ModelOccurrences` prove finite constructor charts and actual reconstruction/FV equations with arbitrary internal child values and typed closed replacements in every PA model. The equal binder returns the original whole quantified word. The fixed-source FV bound and sentence range are now proved in the arithmetic continuation below. |
| Actual sentence chart | `SyntacticSentenceLiteralChart.toSentenceIso`, `toSentence_over`, `toSentence_value`: the literal sentence predicate is isomorphic to the actual chosen sentence object, with its inclusion triangle and formula-coordinate value proved for every T-model, arbitrary T extending PA and arbitrary coefficients. |
| Arithmetic source diagonal component | `ArithmeticDiagonalCodes.diagonalIndex_represents`, `sourceTau_isTuring`, `source_pair_inseparable`, `model_a0`, `model_a1`, `printed_tau_is_universal`, `printed_parity_is_identity`: actual printed-u source morphisms, a PA-total adapter with proved factorization, exact diagonal source equality, PA disjointness and all-PA-model restriction-domain comparisons. These source-diagonal results feed the proved Γ inequalities recorded below. |
| Arithmetic numeral dependency | `NamedArithmeticNumerals` proves the actual internal numeral graph, zero/successor equations and native primitive-recursive certificate. `NamedArithmeticNumeralCarriers.numeralCode_carrier_closed`, `numeralCode_closed` prove accepted term membership and numerical FV=0 for every internal input in every PA model, including nonstandard inputs. `NamedArithmeticNumerals.numeralMorphism` is the actual PA-total graph into closed terms; `numeralCode_standard` proves its exact standard external word. `translateFormula_freeVariables` and its unary specialization prove the external formula FV bound. `NamedArithmeticClosedSubstitution.substitutionFreeFor_closed`, `substitutionResult_closed`, `closedReplacement_PA` prove independent free-for and typed option success for every internal typed formula and typed FV-zero replacement, for arbitrary coefficients in every PA model. `NamedArithmeticFixedSubstitution.value_sentence` and the literal sentence realization below discharge the fixed-formula sentence-range obligation. |
| 7.8, numerical realization | `NumericalDerivationInterpretation.interpretationAlgebraIso`, `mappedDerivationInitial` and both `interpretationCodeIso` word equations compare the actual PA and numerical inference algebras. `NumericalArithmetic.RuleComparison.proofIso`, `branch_constructor`, `inverse_branch_constructor`, `input_label` and `input_children` give the concrete inverse relabellings. `SentenceProofCodes.isPullback`, `ProofComparison.rho_conclusion`, `fixed_provability`, `canonical_forward_program` and `canonical_backward_program` identify the actual sentence image and both canonical computable directions. The literal syntax, substitution, sentence and parameter-stability comparisons are retained. |
| Unnumbered 08d, actual numerical application | `NumericalArithmetic.Incompleteness.theorem_range`, `theorem_support`, `pa_theorems_le`, `domain_inclusions`, `theorem_refutation_disjoint`, `categorical_incompleteness` and `syntax_categorical_incompleteness` identify the actual constructed proof-conclusion image, derive the three diagonal bounds from printed PA-axiom inclusion, use external consistency for disjointness, and apply Corollary 4.3 on both literal and chosen syntax sentence objects. |
| 9.3, actual cosheaf universal property | `ForkInference.inferenceIso` compares the actual ordered rule pullbacks to Ax+M. `ForkDerivation.Component.algebraIso` and `initial` prove the original component proof algebra initial. `constructorComponents_natural`, `foldComponents_natural`, `foldHom`, `fold_unique`, `inferenceInitial`, `printedInitial` and `printed_unique` construct and characterize the global fold. `ForkDerivation.Diagram.shapedInitial` and `shaped_unique` give the printed five-summand presentation on the same realized old carrier and conclusion, for every target slice algebra. |
| 9.4, actual theorem image | `ForkDerivationImages.theoremRange_eq_t0`, `theoremSubobject_isLeast`, `proof_presentation` and `categoricalTheory_eq` identify the constructed initial conclusion image and its bounds. `LiteralDiagram.imageIso`, `imageIso_hom_inclusion`, `theoremObject_eq_t0_domain` and `shaped_theoremSubobject_isLeast` supply the literal numerical image, inclusion and leastness. Consistency retains the printed disjointness hypothesis. |
| 9.6, arbitrary endpoint axiom extensions | `ForkDerivationImages.endpoint_axiom_extension_incomplete` applies to an arbitrary selected endpoint, arbitrary c.e. axiom set, its actual finite derivability relation and ordinary syntactic consistency. The constructed image is identified with the endpoint theory; no compatible extension family is required. |

For the predicate and TotalSplit constructions, initiality assumes only T
extending PA, with arbitrary coefficient predicates,
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

## Arithmetic sentence maps and partial proof search

The following statements use the manuscript's literal sentence realization.
An interpreting arithmetic code model M is distinct from a semantic structure K.
For the indexed construction, B_PA = Tot(Split(S_PA)), E is its identity
Ω object, and S realizes the literal sentence predicate. The family axiom
formula is Ax(e,z) = Sent(z) ∧ (Ax_PA(z) ∨ W(e,z)). Γ_e consists of the
sentences whose codes satisfy Ax(e,z) in N; e is an external natural number
when a numeral fiber is taken.

| Construction | Proved declarations and scope |
| --- | --- |
| Fixed-source substitution and free variables | `NamedArithmeticSubstitutionOccurrences.termOutput_member_iff`, `formulaOutput_member_iff`, `result_sentence` hold for arbitrary coefficient predicates and every PA model. The source formula is externally finite; the typed closed replacement may be an arbitrary internal word. The quantified equal-name branch retains the original word. |
| PA sentence range | `NamedArithmeticFixedSubstitution.value_closed`, `value_sentence`, `value_admissible`, `value_success`, `value_primrec`, `morphism` prove the actual algorithm's range, independent admissibility, successful result, native primitive recursion and supported uniquely total graph. The sole source condition for sentence range is FV(phi) contained in {0}. No range or totality certificate is assumed. |
| Standard word comparison | `NamedArithmeticFixedSubstitution.standard_literal_result` gives the actual named substitution result, its literal code and empty free-variable list. The arithmetic model's Nat cast is compared explicitly with ordinary naturals. `NamedArithmeticUnarySubstitution` applies the construction to any unary arithmetic formula without evaluating its indices. |
| Realization on omega | `SyntacticOmegaRealization.realizeFromOmega`, `realizeFromOmega_underlying`, `realizeFromOmega_graph`, `omegaPoint_value` construct the morphism from the identity omega splitting, its source-morphism equality and model graph. T may be any extension of PA; the codomain predicate and T-supported, T-total graph are arbitrary. No standard model of T is assumed. |
| Literal sentence morphism | `NamedArithmeticLiteralTotal.theta`, `canonical_graph`, `canonical_value_at`, `standard_literal_result` construct omega → J_PA(literalSent), prove its graph at every internal input of every PA model and identify its standard output with the named algorithm. `NamedArithmeticDiagonalLiteralTotal.theta`, `canonical_value_at`, `standard_literal_result` instantiate the actual alpha of `ArithmeticDiagonalCodes`. The predicate object is explicitly typed; its underlying carrier is the original literal sentence predicate. |
| Actual Gamma refutation image | `SyntacticGeneratedAxioms.refutationCarrier_literal`, `refutation_literal_theory` identify the pullback proof image after the actual sentence negation with literal Sent and an existential negative word in the constructed theorem image. The equations hold in all T-models, for arbitrary T extending PA, coefficient objects and enumeration predicate. Chosen sentence codes are compared through their formula-coordinate morphisms. |
| Source inverse images | `NamedArithmeticProofSearch.graphPullCarrier_idem` proves equality of restriction idempotents in the T-provable source quotient for arbitrary represented graphs. `model_predicateIdem` identifies their interpretations with the partial identities on the corresponding truth sets in every T-model. |
| Actual Gamma partial lift | `NamedArithmeticProofSearch.partial_proof_search`, `ell_domain`, `mem_numericalEll`, `ell_comparison` choose the source morphism before the interpreting model and prove its domain, even/odd graph, reversed fibers and coproduct comparison. The model hypothesis is disjointness of the two evidence predicates. No source PA proof of disjointness, consistency, coverage or total search is required. |
| Constructed images and exact diagonal | `negative_refutation_image`, `actual_partial_proof_search`, `sourceTheta_total`, `sourceTheta_graph`, `positive_source_pull`, `negative_source_pull`, `ell_source_fibers`, `diagonal_partial_proof_search` identify those predicates with the constructed Gamma theorem/refutation images, prove their actual PA source inverse-image equalities, and specialize to the chosen diagonal alpha. All internal inputs in every PA model are covered. |
| Printed negation function | `NamedArithmeticProofSearch.negationWord_primrec`, `negationWord_total_PA`, `negationWord_formulaCode`, `negative_eval_word` give a primitive-recursive extension of negation, its literal PA unique-totality graph and exact formula-code equation, and the all-PA-model equation C'(n) iff Prov_Gamma(Neg(Theta(n))). The negation-constructor graph is proved first for arbitrary coefficients and T-model points. |
| Printed Lemma 7.2 | `NamedArithmeticProofSearch.printed_partial_proof_search`, `printed_diagonal_partial_proof_search`, `ell_comparison_inv` prove the generic unary and exact-alpha statements for the actual selected Gamma theorem program at Theta and Neg(Theta). The displayed reversed fibers are those of F_M(ell) followed by the inverse coproduct comparison, and ell is quantified before all models and their disjointness witnesses. This completes Lemma 7.2. |
| Native proof support | `NamedHilbertQuantifiers.all_mono`, `all_congr`, `all_vacuous`, `all_rename_forward`, `all_intro_under`, `exists_intro` are actual finite named proofs for arbitrary coefficients and Gamma. `SyntacticNamedHilbert.replace_axioms` transforms finite proofs using supplied proofs of the individual enumerated sentence axioms. These lemmas do not identify an older proof calculus with the named calculus. |
| Native proof realization | `SyntacticNamedHilbert.native_derives`, `native_realizes`, `native_sentence_theorem`, `native_sentence_numeral_PA` realize every finite named proof in the actual constructed Gamma derivation carrier, using the genuine seven scheme domains, enumerated sentence axioms, generalization and ordered modus ponens. The comparison is standard PA/N, for arbitrary coefficient predicates and Gamma. The individual Sigma1 theorem membership gets its PA numeral proof; no PA consistency assertion is made. |
| Native refutation realization | `SyntacticNamedHilbert.negation_graph_word`, `native_sentence_refutation`, `native_refutation_numeral_PA` send an actual finite proof of negation to the original sentence's constructed refutation image and supply its individual Sigma1 PA numeral proof. The negated word is compared through the actual categorical constructor graph. |
| Open first-order substitution comparison | `ArithmeticNamedOpenTranslation.term_rew`, `formula_rew`, `formula_shift`, `formula_free`, `formula_emb`, `formula_freeFor_bounded`, `term_substitution_rew`, `formula_substitution_rew`, `instance_substitution` prove the structural and exact substitution comparisons for explicit bound/free-name assignments and fresh binder bounds. These are comparisons with the actual named algorithm, with independent free-for proofs; binder names are retained. They do not assume a theorem-level proof translation. |
| First-order native proof steps | `ArithmeticNamedProofConnectives` proves NNF negation/implication and ordered modus ponens, two-way fresh-seed alpha conversion, actual all/exists steps using the proved substitutions, finite-sequent conjunction/cut and guarded quantifier/disjunction proofs. These proofs supply structural cases of the source LK translation; the concrete Γ/PA axiom comparison below now discharges the arithmetic axiom premise. |
| Conditional source proof translation | `ArithmeticNamedProofTranslation.derivation`, `sentence`, `expanded_instance_substitution`, `expanded_instance_proof`, `expanded_instance_refutation` prove the full ten-case LK2 induction, closed-sentence endpoint and numeral-instance transports. The premise is explicit: each individual axiom of the source theory has a native proof of its fixed named translation. It does not assume translation of all source theorems. `ArithmeticNamedAxiomComparison.axiomsAdmissible_PA` now discharges this premise from the actual native `ExtendsPA` condition on the original Γ enumeration. The generic translation remains conditional for arbitrary source theories. |
| Numeral proof transport | `ArithmeticNamedProofNumerals.translate_expandedNumeral`, `expandedNumeral_eq_standard_PA`, `expanded_instance_equivalence_PA`, `expanded_instance_PA`, `expanded_instance_refutation_PA` compare the two numeral conventions with actual PA proofs at every external standard n. Equal semantic values are not used as equality of syntax words. |
| Concrete Γ/PA axioms | `ArithmeticNamedAxiomComparison.PASeed`, `PAAxiom`, `ExtendsPA`, `extendsPA_iff_canonical`, `induction_admissible`, `axiomsAdmissible_PA`, `sentence_PA_of_extendsPA` compare the native arithmetic/order matrices and arbitrary induction, finite universal closures, equality axioms and actual source PA proofs. The final arithmetic endpoints take the printed native Γ-extension condition, with no residual source-axiom-admissibility field. |
| Printed Lemma 7.1 | `NamedArithmeticDiagonalBounds.standard_instance_result`, `instance_theorem_numeral_PA_of_axioms_admissible`, `instance_refutation_numeral_PA_of_axioms_admissible`, `standard_sentences`, `semantic_bounds` supply the exact standard named numeral word, individual finite-proof witnesses and elementary transfer of the two fixed universal sentences. `ArithmeticDiagonalRepresentation.printed_representation` chooses total θ before Γ/M and proves both inequalities for the actual proper sentence-range and negation; PA in M is derived from M≡N. |
| Actual semantic model and evidence | `ArithmeticNamedPresentation.formula_roundtrip`, `sentence_semantics`, `NamedGammaModel.source_consistent_of_extendsPA`, `exists_model`, `NamedGammaEvidenceSoundness.standard_sentence_evidence_disjoint`, `ultrapower_sentence_evidence_disjoint` construct a semantic K from native Γ consistency and discharge the actual standard/ultrapower sentence-range consistency conditions. K remains distinct from arithmetic code models N/M; no PA proof of Γ consistency is asserted. |
| Printed Theorem 7.3 | `ArithmeticDomainExtension.canonical_map_total`, `interpreted_theory`, `interpreted_negation`, `source_noncoverage` identify the actual canonical split-domain interpretation of the Γ conclusion range. `ArithmeticComparisonTarget.comparison_of_evidence_bounds` applies Theorem 4.2 in fixed S_PA; `ArithmeticInternalComparison.internal_comparison`, `total_undecidable_family` discharge the Γ premises and prove source, standard and stated ultrapower incompleteness with the actual total source g. An arithmetic incompleteness theorem is not substituted for the categorical application. |
| Indexed family component of 7.5 | `ArithmeticIndexedAxioms.axiomGraph`, `fiberAxioms`, `carrier_numeral`, `productIso`, `axioms` construct the actual Σ₁ family and its mono into identity Ω × literal Sent. `ArithmeticIndexedRules.rules`, `unary_parameter`, `binary_first_parameter`, `binary_second_parameter` retain the common external parameter and the individual child formulas. `ArithmeticIndexedFamily.initial`, `sentenceTheory_pullback`, `axiomIntroduction_conclusion`, `fold_unique` prove the constructed full-family universal property, sentence image/pullback and constructor/fold laws. The subsequent numeral-fiber and presentation results are listed separately below. |
| Numeral-fiber universal property of 7.5 | `ArithmeticIndexedFibers.sliceEquivalence`, `numeralRuleConclusion`, `numeralInferenceComparison`, `inferenceComparison`, `algebraEquivalence` derive the extensive slice/algebra decomposition from the actual coefficient pullbacks and ordered-premise diagrams. `fiberInitial` proves IsInitial for the actual pullback carrier; `individualFiberAlgebraIso`, `derivation_pullback`, `sentence_pullback` and `sentenceTheory_fiber` give the constructor-preserving independent derivation comparison and the printed sentence/image pullback. These results allow arbitrary Ax_PA and every standard numeral e. |
| Original Γ_e proof presentation | `ArithmeticIndexedFibers.guardIso`, `guard_axioms`, `oldRuleData`, `individual_oldGamma_comparison`, `individual_oldGamma_sentence_conclusion` compare the unchanged named syntax, original logical/Gen/ordered-MP rules and sentence conclusions with the existing Γ_e proof algebra. `individual_oldGamma_model` identifies its literal theorem predicate with the actual individual conclusion image in every PA model. |
| Printed axiom and proof coordinates | `ArithmeticIndexedAxioms.Exponential.printedCarrier`, `carrierIso`, `mono_square`, `realized_square` identify the printed exponential-pair axiom object with the actual family coefficient. `ArithmeticIndexedProvability.printedProductPredicate` and `printedProductIso` supply the manuscript's product predicate D and chart v:J(D)≅E×S. `proofPresentationIso` identifies J(P₀) with the sentence-derivation object P, and `printedConclusion_realization` proves J(γ_c)=v⁻¹cu for γ_c:P₀→D. `printedConclusionIndex_graph_PA`, `printedConclusionIndex_domain_PA`, `printedProvability_comparison_PA` prove the chosen program's graph, exact P₀ domain and uniform Prov comparison in PA. `sentence_range_regular_image` supplies the actual range/image splitting. The intermediate raw pair presentation is compared to the manuscript's exponential pair. |
| Concrete printed inference family | `ArithmeticIndexedPrintedFamily.coefficientData` instantiates the actual axiom mono square in the ordered rule comparison. `initial`, `algebraIso`, `carrierIso_conclusion`, `fiberInitial`, `individualFiberAlgebraIso`, `sentence_pullback` and `sentenceTheory_fiber` prove the printed family and numeral-fiber universal properties and sentence images. `proofPresentationIso` and `printedConclusion_realization` compare the existing P₀ and selected γ_c with this printed initial algebra. |
| PA numeral-fiber provability of 7.5 | `ArithmeticIndexedProvability.provability_numeral`, `programProvability_numeral`, `printedProvability_numeral` hold for every internal word z in every PA model and every standard e. `printedProvability_numeral_PA` proves the universal PA sentence ∀z, Prov(ē,z) ↔ Prov_Γe(z), without a separate sentencehood premise. No representation, axiom-correctness, consistency or soundness field remains in these endpoints. |
| Exact chosen PA enumeration | `ArithmeticIndexedPAEnumeration.axiomCodes_standard` characterizes the chosen Σ₁ predicate in N by the literal named PAAxiom codes, including all seventeen arithmetic/order seeds, actual substitution-certified induction and finite named universal closure. `canonicalClosure_mem` and `fiber_extendsPA` derive the native PA-extension condition for every Γ_e. The native-code characterization is standard; the separate graph and numeral-Prov comparisons above hold in all PA models. |

`ParameterizedTuringDiagonal.parameter_diagonal` and
`arithmetic_parameter_diagonal` supply one source-total g for the joint
partial search. `ArithmeticUniformSearch.lift`, `diagonal`,
`diagonal_equation`, `proofSentenceMorphism` and
`proofSentenceMorphism_value` construct the single morphism q:E→S and
its actual sentence-code value before a numeral e or consistency proof is
given. The search lift remains partial.

`ArithmeticUniformIndependent.positive_fiber`, `negative_fiber`,
`fiber_disjoint`, `alpha_bound` and `beta_bound` derive the required evidence
and bounds from the proved printed Prov comparison and chosen PA enumeration.
`uniform_independent_sentence_codes` excludes the actual theorem image and
its negation preimage at q(ē). `uniform_independent_sentences` identifies that
interpreted word with an actual closed named formula and excludes native
proofs of both it and its negation. This is Theorem 7.6 for each standard
natural e whose Γ_e is externally consistent. Its final hypothesis is that
fiber's ordinary native consistency; PA extension and evidence disjointness
are derived. The independence conclusion uses the standard code model N;
the all-PA-model graph and numeral-Prov equations are separate stronger
presentation statements. It does not infer nonstandard consistency from
external consistency.

`ArithmeticSentenceInseparability.no_recursive_separator` pulls a recursive
separator back through the actual substitution function and uses the proved
partial source realization of its reversed conditional in categorical
Corollary 3.2. `recursively_inseparable`, `sentence_incomplete` and
`extension_incomplete_system` discharge the original Γ consistency/model
and PA-extension premises. The c.e. parallel-enumeration argument is proved
over opaque sets before its actual Γ instantiation; finite axiom replacement
transports the original PA proofs to each extension.

The statement checks spell out the source/model order of quantification and
the actual generated images. The final printed search statement and inverse
coproduct comparison passed production and strict raw checks.
Additional expanded projection and chosen-pullback comparison drafts are
preserved in the ignored continuation area and are not counted as proofs.
They do not change the literal sentence target of the constructed morphism.

## Miller representation independence and category

The literal binary map ρ is continuous and onto, with compact nonempty full
fibers, including dyadic ambiguity and endpoints. Primitive-recursive finite
cylinder coverage and dyadic separation certificates provide an enumerable
finite-cover test. `Unanimity.search_correct` proves that a certificate exists
exactly when all representations halt with the same output. The actual
`OracleProgram.ofTable` compiler gives `Unanimity.unanimityIndex`, chosen before
z, p, e and n. Its graph and domain equations prove the printed τ, including
simultaneous undefinedness. No oracle selection or coherence premise remains.

`Uniform.Object` uses the printed numerical objects. A morphism has one
program before every representation, with equality of its full partial graph.
Constructed instances supply restrictions, ranges, zeros, products, restriction
coproducts, isotypical coding, finite compatible joins, local connectedness and
weak choice. Its Turing morphism is literally `Unanimity.tau`, with ordinary
computable parameter indices. The full characteristic-oracle comparison
`OracleRelative.recursiveIn_iff_index` identifies the singleton-family target
with every partial p-recursive function, preserving values and domains. Its
reverse index is for fixed p; it does not infer a uniform source index from
unrelated pointwise witnesses. The identity-value faithful range functor J
preserves products and finite compatible joins. Source τ is kept distinct
from the target's universal oracle interpreter.

The subsequent Split(Rec^p) carrier presentation and Miller 8.3–8.6 are not
claimed from these endpoints. Scoped source review found no confirmed drift;
completion here is supported by the targeted, statement and full kernel runs.

Development included wall-clock timeouts and ordinary elaboration failures.
No explicit OOM failure was observed. Completed profiled probes used about
2.2 GiB maximum RSS; unsuccessful timeout wrappers do not supply reliable
child-process resource measurements. All evidence is preserved and no
heartbeat limit, linter, toolchain, dependency or axiom policy was relaxed.

The preceding unanimity/category replay at proof `bdfef37` took
1 hour 56 minutes 9 seconds. Its GNU time
profile recorded a maximum resident set of 3,108,560 kB (about 2.96 GiB),
zero swaps and exit 0. No timeout or explicit memory-allocation failure was
observed in that run. The verification record retains the resource-log path
and distinguishes these completed measurements from development timeouts.

## Miller cut reduction and categorical inseparability

`Cut.separatingReal_program` is an unconditional construction of one oracle
program before every p, e and k. Increasing finite halting stages have the
proved bad-set images as finite unions of closed dyadic boxes. The weighted
product distance has constructed nearest points; finite minima and the
empty-set convention give the required positive loci. Primitive-recursive
finite approximation and use algorithms, with proved series tail/error
bounds, produce strict rational approximations to one separating real.
Different representations may return different rational indices.

`Cut.uniform_cut_reduction` specializes that actual program by one ordinary
recursive map chosen before every Miller sequence. The printed Miller
property gives its coordinate equation and both exact inverse images of
the lower and upper cuts. No realizer, cozero or reduction premise remains.
`Cut.printed_cut_contrast` applies the actual source Turing diagonal and
source-conditionals argument, proves internal cut inseparability and gives
the actual first-digit separator for every fixed representation.
`Cut.mapped_tau_notTuring` concerns J of the original source tau in the full
fixed-oracle target; its target oracle interpreter remains distinct.

Two auxiliary pairs construct the actual source inclusion into its splitting
with arbitrary complementary-idempotent recovery, and a single uniform
program for both strict rational coordinate predicates. These are concrete
application constituents, not a completion claim for 8.6. The literal
fixed-p c.e.-carrier comparison is also not inferred from the inclusion.

All 23 producer/check pairs passed the existing targeted and expanded strict
checks; the combined audits and full replay are recorded below. Earlier
proof bodies, manuscript, toolchain, dependencies and source pins are unchanged.
The ignored 8.5 syntax/list/derivation/total-category and generated-theory
proof bodies remain uncompiled and excluded from completed-result claims.

The cut batch's completed full replay at proof `f15eeb1f562d4d081edefb67821ca6b1a4ca57e9` took
`2:03:36` wall-clock time. Its GNU time profile recorded
3,115,672 kB maximum resident set size
(2.97 GiB), zero swaps and exit 0.
No wall-clock timeout or explicit memory-allocation failure occurred in
this full run. Resource log: `.codex-work/v48-miller-cut-full-f15eeb1-resource.log`. Historical development
timeouts and elaboration failures remain preserved separately.

## Verification and source identity

The preceding complete v47 run is preserved at
`.codex-work/verify-20261106T000653Z-wVCQvv`: 783 successful commands,
1,274 retained and 10,610 current declarations, 406 production modules,
1,065 inputs and snapshot SHA-256
`0b6c1df38427b837b9998f08335ea8e2bcf1ef863170bfea1959b09ba191b019`.
Every input matched at the beginning of that earlier continuation. Earlier v46 baselines
and the original 516-input reviewed snapshot remain in the committed history.

The baseline current-manuscript v47 `bash scripts/verify-wsl.sh` passed with exit **0** under the
existing lock and `LEAN_NUM_THREADS=1`. Run: `.codex-work/verify-20261106T052422Z-MLM1qM`.
All 837 commands passed: combined build, both statement audits,
every strict source/check replay and transitive axioms. The audit retains
all 1,274 earlier declarations and covers 11,129 current-production declarations in
433 production modules. Its axiom union is exactly `propext`, `Quot.sound`,
`Classical.choice`. All 16 dependencies were clean and pinned at start/end;
356 imported-source pins and 25 current manuscript files and artifacts passed.
All 1119 tested inputs match committed bytes at proof commit
`16ec62198d0aaa6506fc50d949f35af0fb26d94d`, whose ordinary main push and remote ref were confirmed.
Source-snapshot SHA-256: `4902b616aff33dd2018f304ddfd722c20f451ce97b3ce3582dca8ad56bb77209`.
The separate report commit and Downloads copies are checked by the existing
committed-byte delivery procedure.

The subsequent arithmetic application and indexed-family components have completed
targeted production builds and strict raw statement checks. Their frozen source hashes
and preserved command logs are recorded below. The 905-command core run is
historical baseline evidence. The completed current integrated result is recorded below.

| Completed layer | Freeze evidence and successful production results |
| --- | --- |
| Concrete PA axiom comparison | `.codex-work/v46-concrete-named-comparison/first-order-bridge-freeze.json`, batches `axiom_basic`, `axiom_matrices`, `axiom_equality`, `axiom_induction`, `axiom_comparison`; production results at `production-20261106T083658433995Z`, `20261106T085207399844Z`, `20261106T090251787577Z`, `20261106T090628354002Z`, `20261106T090725261977Z` in that directory. |
| Standard/model Γ bounds | `.codex-work/v46-named-arithmetic/V46NamedArithmeticDiagonalBounds-FROZEN.json`; its five successful production result records are `20261106T084116681551Z`, `20261106T084203597554Z`, `20261106T084253117244Z`, `20261106T084342490121Z`, `20261106T090845207821Z` on 6 November 2026. |
| Semantic model, evidence and final 7.3 | `.codex-work/v46-concrete-named-comparison/native-model-FROZEN.json`; production `20261106T091010814913Z`, evidence `20261106T094957596295Z`, final `20261106T103331664464Z`. |
| Proper sentence model and categorical target | `.codex-work/v46-named-arithmetic/V46ArithmeticComparisonTarget-FROZEN.json`; successful production result records `20261106T102552742596Z`, `20261106T100513138500Z`, `20261106T102133783302Z`, `20261106T102848601183Z`. |
| Canonical split extension and final 7.1 | `.codex-work/v46-named-arithmetic/V46ArithmeticDomainExtension-FROZEN.json`; successful production result records `20261106T092821336420Z`, `20261106T102236876778Z`, `20261106T102411278989Z`. |
| Indexed axiom/rule/full-family construction | `.codex-work/v46-named-arithmetic/V46ArithmeticIndexedFamily-FROZEN.json`; combined strict scratch `20261106T103956096890Z`, production `20261106T104026121473Z`, `20261106T104112265861Z`, `20261106T104145897540Z`. This is the historical full-family layer; the later fiber proof has its own receipt below. |
| Parameterized source equation for 7.6 | `.codex-work/v46-named-arithmetic/V46ParameterizedTuringDiagonal-FROZEN.json`; strict scratch `20261106T105641053627Z`, all four production/strict commands in `production-20261106T105711299864Z` passed. |
| Direct categorical Corollary 7.4 | `.codex-work/v46-concrete-named-comparison/first-order-bridge-freeze.json`; conditional and diagonal layers, Core `production-20261106T104620714808Z`, final `production-20261106T111723708548Z`; all 16 production/strict commands for the eight files passed. |
| Actual numeral fibers and original Γ_e comparison | `.codex-work/v46-concrete-named-comparison/native-fibers-FROZEN.json`; 26 source/check files, 52 successful production/strict commands. Main fiber pair `production-20261106T173808180182Z`; generic inference transport `20261106T174158641863Z`; final old-Γ presentation `20261106T175102057140Z`. All earlier predicate, numeral, axiom and constructor components are enumerated in that receipt. |
| Concrete printed-family specialization | The same native receipt includes `V46ArithmeticIndexedPrintedFamily` and its raw statement checks: strict `20261107T033502882066Z` and all four production/strict commands in `production-20261107T033531627341Z` passed. The coefficient, algebra, numeral-fiber, sentence-image and P₀ conclusion comparisons use the printed exponential coefficient. |
| Exact chosen PA enumeration | `.codex-work/v46-named-arithmetic/V46ArithmeticIndexedPAEnumeration-FROZEN.json`; twelve files, 24 successful production/strict commands, final actual induction/enumeration batch `production-20261106T154300307551Z`. |
| Printed exponential axiom/program coordinates | `.codex-work/v46-named-arithmetic/V46ArithmeticIndexedExponential-FROZEN.json`; program presentation `production-20261106T161404518834Z`, restricted axiom coefficient `20261106T163629288347Z`, all eight production/strict commands passed. |
| Actual P₀/index/image and PA numeral-Prov comparison | `.codex-work/v46-named-arithmetic/V46ArithmeticIndexedProvability-FROZEN.json`; source/model/presentation layers and final `production-20261106T175328411220Z`, including the completed comment-only replay. All recorded commands passed. |
| Uniform joint search, one q and actual 7.6 | `.codex-work/v46-concrete-named-comparison/first-order-bridge-freeze.json`, uniform family component; final `production-20261106T175744488479Z` passed all four production/strict commands. The generic joint lift, one-source-g sentence composite and predicate layers have their successful component records in the same receipt. |

Each abbreviated production stamp denotes the existing `production-<stamp>/results.json`
in the stated work directory. The retained 7.2 source search and decoded-fiber results
are separately frozen in `.codex-work/v46-named-arithmetic/V46NamedArithmeticProofSearch-FROZEN.json`
and were included in the preceding full verified checkpoint.

The last completed core-baseline v47 `bash scripts/verify-wsl.sh` passed with exit **0** under the
existing lock and `LEAN_NUM_THREADS=1`. Run: `.codex-work/verify-20261106T125901Z-Acu0zJ`.
All 905 commands passed: combined build, both statement audits,
every strict source/check replay and transitive axioms. The audit retains
all 1,274 earlier declarations and covers 11,812 current-production declarations in
467 production modules. Its axiom union is exactly `propext`, `Quot.sound`,
`Classical.choice`. All 16 dependencies were clean and pinned at start/end;
356 imported-source pins and 25 current manuscript files and artifacts passed.
All 1187 tested inputs match committed bytes at proof commit
`e08d21c7eee33e6e7ee398411124039133a92905`, whose ordinary main push and remote ref were confirmed.
Source-snapshot SHA-256: `d96d2d6e3e15b2166bdc3b748e31b8038c73e8b55e4158af1889447bf103d075`.
The separate report commit and Downloads copies are checked by the existing
committed-byte delivery procedure.

Report commit `1db7a66` records that completed core baseline and its checked
committed-byte delivery. The indexed 7.5–7.6 proof batch is subsequent work.

The intermediate 58-file indexed batch also completed full verification: run `.codex-work/verify-20261106T180328Z-2ogkTV`, exit 0, all 963 commands passed, 1,245 tested inputs, 13,224 current-production declarations in 496 modules and the same three permitted axioms. Snapshot SHA-256: `3f35a20b64bfb53459ef920167d689bec2c62e6a0b2c517ba80af7710b9eb5da`. The final batch additionally includes the explicit two-file printed-family specialization and its updated imports/correspondence.

The preceding complete v48 `bash scripts/verify-wsl.sh` passed with exit **0** under the
existing lock and `LEAN_NUM_THREADS=1`. Run: `.codex-work/verify-20261108T114347Z-mULAhc`.
All 1263 commands passed, including combined build, statement audits,
every strict source/check replay and the transitive axiom audits. The audit
retains all 1,274 earlier declarations and covers 19,101
current-production declarations in 646 production modules.
Its axiom union is exactly `propext`, `Quot.sound`, `Classical.choice`.
All 16 dependencies were clean and pinned at start/end;
356 imported-source pins and 25 manuscript files/artifacts passed.
The frozen wrapper started at proof commit `f15eeb1f562d4d081edefb67821ca6b1a4ca57e9`; all
1545 tested inputs match that commit's bytes and remained unchanged.
Its ordinary main push and remote ref were confirmed.
Source-snapshot SHA-256: `3a3801254c0604b2549727ba171a8d212d06540af707c5ed803e68c37867fa78`.
Miller 8.1–8.4 are complete. The cut reduction has no residual approximation
or reduction premise, and the inseparability/relative-separator comparisons
use the actual source Turing morphism and full fixed-oracle interpretation.
Miller 8.5 and 8.6 remain open. There are 60 closed rows among 62 numbered results; this is coverage, not a
percentage of proof effort. Earlier arithmetic, numerical and cosheaf results
remain proved. The separate report commit and Downloads copies are checked by
the existing committed-byte delivery procedure.

The first full replay of that core batch,
`.codex-work/verify-20261106T112013Z-4QlbST`, completed all 905 Lean commands
with exit 0, then the existing lexical source gate matched the English
phrase “sets admit no” in a documentation comment and returned exit 1.
The comment was changed to “sets have no”; theorem statements, proof terms,
axioms and verifier checks were unchanged. The repaired pair passed four
production/strict commands, every production file passed the unchanged
lexical rule, and the complete rerun reported above passed with exit 0.
Both full runs and the repair evidence are preserved in the verification record.

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

## Miller realization, verified at the recorded proof commit

The actual uniform carrier category now has its total-splitting equivalence,
regularity, extensivity and partial-map equivalence. The construction returns
fiber-constant values when descending a surjection and the unique inverse
value for a monomorphism. It does not supply arbitrary surjection sections.
The public endpoints include `Miller.Total.pointPresentation`,
`totalRegular`, `totalFinitaryExtensive`, `partialMapEquivalence` and
`mono_has_partial_inverse`.

For arbitrary uniform coefficient objects and every parameter object R,
the literal word fold now commutes with every constructor. The graph of
every actual algebra morphism satisfies the derived constructor root laws;
structural word induction proves uniqueness among all such morphisms.
`Miller.Syntax.Raw.parameterFoldHom_unique` and `explicitWordInitial` package
that universal property. The constructed `constantPolynomialSquare` and
`parameterWordAlgebraIso` transport it to the canonical parameter algebra,
yielding `wordWithParametersInitial` and `wordInitial`. Operations remain
arbitrary supported uniform morphisms, total on their actual carriers;
no ordinary recursive or PA-total extension is required. Coefficient guards,
named variables and ordered children are retained.

The literal fixed-p target presentation also has a proved restriction
comparison: `Miller.RelativeCarriers.splitEquivalence`, `morphism_iff` and
`totalEquivalence`. `Miller.CarrierIdempotents.supportOrderIso` identifies
idempotents on a carrier A with the appropriate semidecidable subsets of A;
its top has support A. This does not assert fullness of the all-representation
interpretation J into the fixed-oracle target.

The stable list fold has nil/adjoin equations and uniqueness in every parameter slice; `Miller.Lists.stable` transports through the actual literal list-word algebra isomorphism. `Miller.Syntax.canonicalCategoricalSyntax` supplies the syntax/list instance in the actual total splitting. `Miller.Derivation.Canonical.derivationInitial` constructs the arbitrary-rule initial algebra there. Each child has its prescribed premise as conclusion; only an external parameter is shared. The successful pullback retains rule labels and ordered children, including nullary rules. Its `fold_underlying_unique` quantifies over every morphism satisfying the original conclusion and constructor equations. `Miller.FirstOrder.proofInitial` instantiates all seven schemes, generalization and ordered modus ponens for every axiom subobject. `generatedSentence_least` and `sentence_idempotent_represents` prove the actual least sentence image and its restriction idempotent. No initiality, consistency, decidability or soundness premise is added.

These 78 producer/Checks pairs have 312 successful production commands and
156 successful independent strict scratch checks, with all 156 canonical
file hashes rechecked. They are imported by the main production entry point,
`CurrentStatementAudit` and the retained `V46StatementAudit`. Automatic
transitive axiom coverage and the full integrated replay passed in `.codex-work/verify-20261108T203846Z-oUfIlw`
at `86b33eca560e389ac557e6d27b21e67a20b13c75`. The prior f15eeb1 snapshot remains historical baseline evidence. Stable lists and arbitrary-rule derivations now complete
the concrete canonical bundle of 8.5. The field-theory,
named proof-image and categorical application proofs of 8.6 remain separate.

The full baseline used 2:03:36 elapsed time, reported maximum RSS 3,115,672 KiB,
zero swaps and exit 0. The new development encountered a heartbeat limit and
a 45-second source-check cutoff in polynomial comparison proofs. Explicit
morphism types, local composition lemmas and complete constructor diagrams
removed those failures without increasing limits or disabling linters; the
repaired producers and imported Checks passed. A final first-order statement check
also encountered the 45-second cutoff. Making its dependent axiom binder explicit
in each example preserved all 26 intended claims and passed the independent
strict and production checks. A separate imported axiom control confirmed only
the three permitted axioms; the new full integrated audit now confirms that same union. Retained logs show no confirmed
out-of-memory failure. These resource observations do not measure aggregate
host memory usage.

## Concrete Miller field and axiom comparisons, 8 November

The next thirty-four producer/Checks pairs have 136 successful production commands
and 68 successful independent strict source checks. Twelve compare the literal
word and list algebras and construct `presentedSyntax` and
`canonicalPresentedSyntax`. They derive target initiality independently; the
predicate interpretation F is not assumed faithful or to preserve initiality.
The finite-power and constructor-polynomial normalization is proved explicitly.
The intrinsic list folds preserve branching, equality, singleton, ordered append,
membership and deletion under the actual chart.

Three additional pairs prove the actual option/product comparisons, including
failure and successful values, and the constant-family product/coproduct diagrams
before and after an arbitrary base isomorphism. Coefficient morphisms and the two
parameter objects remain explicit. They use only finite geometry; the predicate
functor is not assumed to preserve initiality. All fourteen expanded option
checks and the six/eight family and base-change checks pass independently.
The full polynomial parameter comparison remains under development.

The eleven field-theory pairs construct the arity-two ordered-field language,
primitive-recursive membership in all literal sentence words, the actual
recursive RCF axiom words and the uniform rational-cut enumeration. The exact
sentence is `2*c_n<1`. `RealClosedBounds.lower_cut_gamma_theta` and
`upper_cut_gamma_negtheta` construct finite native Gamma proofs under the
printed derivability-extension condition. `extends_iff_proof_transport` uses
finite axiom replacement; it adds no literal axiom-inclusion or Gamma-truth
premise. The negative bound uses the actual named substitution instances.

`RealClosedRaw.modelsRCF_iff_exists_realization` starts with an arbitrary total
named interpretation, extracts all sixteen finite field/order matrices, and
constructs a real-closed ordered field on the same carrier. Its function,
constant and relation equations retain every original interpretation value.
No supplied field or order structure is a premise. The real field with the
actual constants a(n) models the selected T_a words, and actual finite-proof
soundness proves native consistency of T_a. These semantic constructions do
not assume truth of an arbitrary consistent Gamma.

Two further pairs construct the actual uniformly semidecidable axiom
subobjects and genuine sentence-word pullbacks. `SentenceAxiomPullbacks.givenPresentation`
recovers every given axiom mono by its image codes. Sentence-point codes and
formula words remain distinct. The finite carrier alone is represented by a
PA predicate; arbitrary Gamma is not assumed PA definable. Inverses are used
for monomorphisms, with no section of a proof-conclusion image.

Six word-induction pairs supply constructor decomposition of the actual
successful derivation word, strict rank decrease for each ordered child with
its own prescribed conclusion, and induction for any external predicate.
`Miller.Derivation.WordInduction.word_rule_induction` and
`conclusion_induction` use the proved initial algebra. The concrete
`firstOrder_conclusion_induction` includes logical and Gamma nullary leaves,
generalization and ordered modus ponens. No decidability or definability
condition is imposed on the induction predicate.

The immutable targeted receipts are `miller-named-syntax-first12-FROZEN.json`,
`miller-field-theory-FROZEN.json`, `miller-axiom-subobjects-FROZEN.json` and
`miller-derivation-word-induction-FROZEN.json` in
`.codex-work/v46-concrete-named-comparison/`. Main and both statement audits
import the completed pairs; full automatic axiom coverage and serialized replay
passed at `86b33eca560e389ac557e6d27b21e67a20b13c75` in `.codex-work/verify-20261108T203846Z-oUfIlw`. These components do not close Theorem 8.6. Its remaining named
substitution/admissibility, native derivation-image and canonical comparisons,
and the final categorical application are still open.

An uncompiled application draft used all-formula native consistency, stronger
than the manuscript's sentence consistency. The source-only repair restricts
it to closed sentences and proves the intended equivalence with the actual
sentence-idempotent disjointness equation. That repair and its direct printed
application endpoint remain uncompiled, and are not counted as completed.
No manuscript statement was changed.

## Targeted comparison continuation after the completed full replay

Five further producer/Checks pairs have passed targeted verification after proof `86b33ec`: the named occurrence-fold comparison, the actual option-success pullback, and the canonical constructor, transpose and operation comparisons. `NamedSyntaxComparison.occurrence_fold_comparison` uses algebra-morphism uniqueness to identify the full occurrence fold; `termOccurrences_comparison` and `formulaOccurrences_comparison` are its components. `NamedSyntaxComparison.Options.success_isPullback` and `successIso_fst`/`successIso_snd` compare the actual success pullbacks. Through the genuine equivalence `E = Total.pointPresentation a`, `CanonicalPresentation.forward_constructor` and `forward_fold` compare constructors and folds; `termSubstitution_comparison`, `formulaSubstitutionOption_comparison`, `admissibleIso_inclusion`, `admissibleIso_result` and `negation_comparison` give the canonical operation diagrams. These canonical E comparisons are distinct from the remaining named substitution and derivation-image comparisons for the finite-geometry functor F.

Each of the five frozen pair receipts records two successful strict scratch commands and four successful production commands, including an independently imported Checks module: 30 commands in total. The producers are imported by the main entry point, the Checks modules by `CurrentStatementAudit`, and both axiom audits import the main entry point. The separate manuscript-only gate `run/comparison-five-manuscript-gate-20261109T003131805695Z.json` exited 0. No new combined Lean build, transitive axiom audit or full replay is asserted for these additions. The last completed full replay remains proof `86b33eca560e389ac557e6d27b21e67a20b13c75`, with 1,487 commands and snapshot `8a65beb3d802488e970d729485bb535ef1fd5f3704f93e7fdb2fd460777cd851`; its measured declaration/module counts, raw verifier and source-hash list remain unchanged.

Theorem 8.6 remains open. The remaining principal steps are the named substitution/admissibility and finite native-proof/sentence-image comparisons for F, the remaining canonical sentence/inference/derivation-image transport with recovery of an arbitrary original axiom mono, and the actual Corollary 4.3 application. No truth hypothesis on Γ or uniform proof selector is supplied. The five targeted pairs do not change the count of completed numbered results.

Five additional producer/Checks pairs now have 30 successful targeted commands: the actual Option constructor cases, all seven syntax constructors and both algebra structure equations, substitution parameter/state charts, and every quantified and nonquantified substitution branch. In particular, `equal_name_keeps_original_with_recursive_failure` proves the equal-binder branch retains the original body even when the recursive result is `None`. These arbitrary-coefficient equations are imported by the production and intended-statement entry points. They do not yet identify the full substitution fold: parameter-slice transport, its algebra morphism and uniqueness remain pending. The two post-full batches comprise ten pairs and 60 successful targeted commands. New integrated full verification remains pending, and the recorded full-run source snapshot and counts remain unchanged.

## Remaining mathematical dependencies

The concrete Γ/PA axiom comparison, standard finite-proof bounds, elementary
transfer and proper sentence-object inequalities complete Lemma 7.1.
The actual semantic model, soundness factor and partial-search lift now
instantiate Theorem 4.2, completing the source, standard and stated
ultrapower conclusions of Theorem 7.3. The direct recursive-separator argument of Corollary 7.4, its actual c.e. parallel-enumeration consequence and every consistent c.e. extension are also proved.

Proposition 7.5 now has the constructed full family, complemented numeral
slice and inference/algebra equivalences, actual fiber initiality, original
Γ_e derivation comparison, sentence pullback/image, printed exponential
A₀/D/P₀ coordinates and selected-program PA numeral-Prov equivalence.
Theorem 7.6 now has one total q:E→S with the stated independence at each
externally consistent standard fiber, using the actual chosen PA enumeration.

Proposition 7.8 and the actual numerical 08d application remain proved.
Cosheaf 9.3 and its 9.4/9.6 identifications are complete. Miller 8.1–8.4
are complete. Proposition 8.5 now has its actual carrier geometry, syntax/list and arbitrary-rule
derivation realization, including the canonical first-order bundle. These proofs passed the integrated full verification recorded above. The remaining numbered Miller result is 8.6,
the F named substitution/admissibility and finite native-proof images, remaining canonical sentence/inference/proof-image transport and categorical application. The concrete field/RCF constituents remain proved; the five new comparison pairs have targeted verification only.
Ignored source-only bodies do not complete that obligation. There are 61 proved rows
among 62 numbered results, with 8.5 included in the completed integrated verification;
this is coverage rather than a percentage of proof effort.

Semantic K is distinct from arithmetic code models N/M. External Γ
consistency is not a PA proof of Γ consistency. The fixed universal
sentences used for 7.1 cover all elements of M≡N by elementary transfer;
this is not a claim that nonstandard codes are external finite proofs.
The proof-search lift remains partial. Exponential/parity object coding
and the uniform computation comparison are separate completed proofs.

Rows 9.1 and B.10 retain the corrected status of the completed numerical tuple comparison
in 7.7. Manuscript editing belongs to the manuscript chat; this proof
batch preserves its integrated target.

<!-- V46_CURRENT_VERIFICATION_START -->
The current-manuscript v48 `bash scripts/verify-wsl.sh` passed with exit **0**
in `.codex-work/verify-20261108T203846Z-oUfIlw` at tested proof `86b33eca560e389ac557e6d27b21e67a20b13c75`. All 1487 recorded commands
passed. The transitive audits retain 1,274 earlier declarations
and cover 22,790 current declarations in
758 production modules. The permitted union is
exactly `Classical.choice`, `Quot.sound`, `propext`. All 16 dependency worktrees
were clean and pinned at start/end; 356 imported-source
pins and 25 manuscript artifacts passed.

All 1769 measured input hashes match committed proof `86b33eca560e389ac557e6d27b21e67a20b13c75`;
snapshot SHA-256: `8a65beb3d802488e970d729485bb535ef1fd5f3704f93e7fdb2fd460777cd851`. No measured bytes
changed during the full replay. The ordinary proof push and remote ref were checked.
The measured verifier JSON and source-hash list remain tied to this proof commit.

Proposition 8.5 is complete. Its 78 producer/Checks pairs and the
34 completed 8.6 component pairs are covered by this full replay.
Theorem 8.6 remains the first open principal result; its final named proof-image,
canonical-presentation and Corollary 4.3 application drafts remain uncompiled.
There are 61 proved rows among 62 numbered results; this is coverage, not proof effort.

After the replay, only verification wording in `FORMALIZATION_STATUS_V48.md` was amended.
Its before/after hashes, exact permitted patch and separate successful manuscript-only
gate are recorded under `post_verification_correspondence`; these amended documentation
bytes are not claimed as inputs to the earlier Lean replay. Every other measured input
is unchanged. All six delivered payloads come from the separately pushed report commit.

Completed wrapper resources: elapsed 3:19:33, maximum RSS
3,410,772 KiB, swaps 0, exit 0.
These are GNU time measurements, not an aggregate host-memory estimate.
<!-- V46_CURRENT_VERIFICATION_END -->

<!-- V48_SENTENCE_COMPONENT_PROGRESS_START -->
Seven additional producer/Checks pairs pass all 42 targeted commands after `729021e`. The actual F sentence pullback, inclusion, negation and sentence-point/formula-word graph are compared. Named proof data now supplies actual sentence points, arbitrary uniformly enumerable Γ axiom leaves and the constructed finite-derivation carrier and conclusion. The genuine E equivalence compares the canonical sentence and Γ axiom pullbacks. `TheorySentenceMorphisms.theta` is total before Γ is chosen; its graph/value equations and sentence negation equations use the fixed integer-coefficient field syntax and the proper chosen sentence object.

The actual canonical list/constructor and membership squares and native implication, equality and quantifier point equations also pass their independent checks. The native term/formula point bijections and inverse code equations are also proved, including exact named-binder and negation decoding. These results keep the native finite-proof image comparison separate from construction of the derivation carrier. The F substitution-fold/admissibility comparison, native proof-image equations, remaining canonical logical/inference/derivation-image comparison and recovery of an arbitrary original axiom mono, and the actual Corollary 4.3 application remain open. The latest seven pairs add to the ten previously recorded targeted pairs: 102 successful targeted commands after the unchanged full run at `86b33ec`. New combined verification and transitive axiom coverage remain pending; Theorem 8.6 is still partial and the numbered coverage remains 61 of 62.
<!-- V48_SENTENCE_COMPONENT_PROGRESS_END -->

<!-- V48_NATIVE_REFLECTION_SUBSTITUTION_PROGRESS_START -->
Five further producer/Checks pairs pass all 30 targeted commands after `bb8a670`. `NamedProofImage.sentence_inclusion_closed`, `axiom_word_member` and `axiom_finite_proof` recover literal closed Γ axioms from the actual sentence pullback and give singleton finite supports. `generalization_finite` retains a child's finite support; `modusPonens_finite` combines the ordered antecedent and implication supports through native axiom replacement. These statements impose no truth hypothesis on Γ and choose no family of Γ proofs.

`NamedProofImage.NativeSubstitution.PointFrame.realize_natural` gives finite framed polynomial inputs at an actual parameter. `optionEquiv`, `option_graph`, `success_iff` and `failure_iff` identify every native Option point with its actual categorical value, success pullback or failure branch. The success/failure statements concern the decoded categorical result; the full native substitution induction remains a separate dependency.

`term_root_framed` and `formula_root_framed` prove the actual substitution fold's constructor equations on those framed inputs. `function_node_map` preserves the selected symbol and ordered children. `equal_binder_option`, `equal_binder_decoded`, `equal_binder_success` and `equal_binder_reflection` prove the whole Option result retains the original quantified formula when the binder equals the query, including when recursive substitution into its body fails.

The post-full continuation now comprises 22 pairs and 132 successful targeted commands. This batch's exact source hashes and six-command receipts are recorded separately from the unchanged full `86b33ec` replay: 1487 commands, 1769 inputs and snapshot `8a65beb3d802488e970d729485bb535ef1fd5f3704f93e7fdb2fd460777cd851`. New combined verification and automatic axiom coverage remain pending. Full native term/formula substitution induction and independent admissibility, the native finite-proof/image equivalence, remaining canonical logical/inference/derivation-image transport and original-mono recovery, and the actual Corollary 4.3 application remain open. Theorem 8.6 remains partial, with 61 of 62 numbered results proved.
<!-- V48_NATIVE_REFLECTION_SUBSTITUTION_PROGRESS_END -->

<!-- V48_NATIVE_TERM_COMPARISON_PROGRESS_START -->
Six further producer/Checks pairs pass all 36 targeted commands after `069d121`. `NativeSubstitution.Standard.rawCode_represents`, `liftData_comparison`, `operation_value` and `pure_operation_value` identify actual standard PA polynomial inputs and their parameter fibers. `PointFrame.realize_parameterComparison`, `realize_parameterTerm`, `realize_parameterFormula` and `nodeBaseArrow_code` compare the actual uniform framed nodes while preserving coefficient labels, binder names and ordered children. `term_node_realizes_hom` and `formula_node_realizes_hom` give their actual morphism equations.

`pa_term_value`, `pa_formula_option_value`, `paTermState_native` and `paFormulaState_native` calculate the standard source values. `expectedTermState_native` and `expectedFormulaState_native` identify the corresponding transported expected states. `Standard.framed_operation_transport_normalized` compares the actual operation on finite framed inputs. The source formula calculation and expected-state chart remain separate from equality with the actual uniform formula-substitution fold.

Native finite-term induction now proves `termState_comparison` and the unconditional `termValue_eq_native`: for every uniform family P, coefficient carriers σ and π, arity bound d, query x, replacement term t and input term r, the actual uniform term-substitution value is the named point of `r.substitute x t`. The checks also expose the original literal word graph and the variable, function and nullary cases.

The post-full continuation now comprises 28 pairs and 168 successful targeted commands. The actual formula Option comparison and independent admissibility remain the first unresolved step, followed by Γ finite-proof/sentence-image equivalence, remaining canonical logical/inference/derivation-image transport and recovery of an arbitrary original axiom mono, and the actual Corollary 4.3 application. Formula drafts are excluded from this checkpoint. Theorem 8.6 remains partial and numbered coverage remains 61 of 62. The historical full `86b33ec` replay retains 1487 commands, 1769 inputs and snapshot `8a65beb3d802488e970d729485bb535ef1fd5f3704f93e7fdb2fd460777cd851`; no new full replay or automatic axiom count is claimed.
<!-- V48_NATIVE_TERM_COMPARISON_PROGRESS_END -->
