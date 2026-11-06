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
the categorical application 7.3 are now proved. The current batch also
constructs the indexed axiom/rule family and its initial algebra, while
keeping numeral-fiber initiality and the uniform sentence morphism open.

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

## Arithmetic sentence maps and partial proof search

The following statements use the manuscript's literal sentence realization.
An interpreting arithmetic code model M is distinct from a semantic structure K.

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
| Indexed family component of 7.5 | `ArithmeticIndexedAxioms.axiomGraph`, `fiberAxioms`, `carrier_numeral`, `productIso`, `axioms` construct the actual Σ₁ family and its mono into identity Ω × literal Sent. `ArithmeticIndexedRules.rules`, `unary_parameter`, `binary_first_parameter`, `binary_second_parameter` retain the common external parameter and the individual child formulas. `ArithmeticIndexedFamily.initial`, `sentenceTheory_pullback`, `axiomIntroduction_conclusion`, `fold_unique` prove the constructed full-family universal property, sentence image/pullback and constructor/fold laws. The numeral-fiber universal property, per-e derivation/sentence pullback comparison and uniform Prov(e,z) presentation remain open. |

`ParameterizedTuringDiagonal.parameter_diagonal` and its actual arithmetic
specialization `arithmetic_parameter_diagonal` prove the source equation for
7.6: one total g realizes the two-input partial lift on the diagonal. The
uniform indexed proof-search lift, chosen PA-axiom enumeration comparison,
numeral-fiber provability comparison and actual sentence morphism q remain
open. These source equations do not assert the completed uniform sentence theorem.

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
and preserved command logs are recorded below. The integrated verification below replays every imported production and statement-check file and compares its tested bytes with the proof commit.

| Completed layer | Freeze evidence and successful production results |
| --- | --- |
| Concrete PA axiom comparison | `.codex-work/v46-concrete-named-comparison/first-order-bridge-freeze.json`, batches `axiom_basic`, `axiom_matrices`, `axiom_equality`, `axiom_induction`, `axiom_comparison`; production results at `production-20261106T083658433995Z`, `20261106T085207399844Z`, `20261106T090251787577Z`, `20261106T090628354002Z`, `20261106T090725261977Z` in that directory. |
| Standard/model Γ bounds | `.codex-work/v46-named-arithmetic/V46NamedArithmeticDiagonalBounds-FROZEN.json`; its five successful production result records are `20261106T084116681551Z`, `20261106T084203597554Z`, `20261106T084253117244Z`, `20261106T084342490121Z`, `20261106T090845207821Z` on 6 November 2026. |
| Semantic model, evidence and final 7.3 | `.codex-work/v46-concrete-named-comparison/native-model-FROZEN.json`; production `20261106T091010814913Z`, evidence `20261106T094957596295Z`, final `20261106T103331664464Z`. |
| Proper sentence model and categorical target | `.codex-work/v46-named-arithmetic/V46ArithmeticComparisonTarget-FROZEN.json`; successful production result records `20261106T102552742596Z`, `20261106T100513138500Z`, `20261106T102133783302Z`, `20261106T102848601183Z`. |
| Canonical split extension and final 7.1 | `.codex-work/v46-named-arithmetic/V46ArithmeticDomainExtension-FROZEN.json`; successful production result records `20261106T092821336420Z`, `20261106T102236876778Z`, `20261106T102411278989Z`. |
| Indexed axiom/rule/full-family construction | `.codex-work/v46-named-arithmetic/V46ArithmeticIndexedFamily-FROZEN.json`; combined strict scratch `20261106T103956096890Z`, production `20261106T104026121473Z`, `20261106T104112265861Z`, `20261106T104145897540Z`. This evidence does not claim numeral-fiber initiality. |
| Parameterized source equation for 7.6 | `.codex-work/v46-named-arithmetic/V46ParameterizedTuringDiagonal-FROZEN.json`; strict scratch `20261106T105641053627Z`, all four production/strict commands in `production-20261106T105711299864Z` passed. |
| Direct categorical Corollary 7.4 | `.codex-work/v46-concrete-named-comparison/first-order-bridge-freeze.json`; conditional and diagonal layers, Core `production-20261106T104620714808Z`, final `production-20261106T111723708548Z`; all 16 production/strict commands for the eight files passed. |

Each abbreviated production stamp denotes the existing `production-<stamp>/results.json`
in the stated work directory. The retained 7.2 source search and decoded-fiber results
are separately frozen in `.codex-work/v46-named-arithmetic/V46NamedArithmeticProofSearch-FROZEN.json`
and were included in the preceding full verified checkpoint.

The required current-manuscript v47 `bash scripts/verify-wsl.sh` passed with exit **0** under the
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

The first full replay of this batch,
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

## Remaining mathematical dependencies

The concrete Γ/PA axiom comparison, standard finite-proof bounds, elementary
transfer and proper sentence-object inequalities complete Lemma 7.1.
The actual semantic model, soundness factor and partial-search lift now
instantiate Theorem 4.2, completing the source, standard and stated
ultrapower conclusions of Theorem 7.3. The direct recursive-separator argument of Corollary 7.4, its actual c.e. parallel-enumeration consequence and every consistent c.e. extension are also proved.

The indexed axiom mono, parameter-preserving finite inference signature and
full-family initial algebra are proved. Proposition 7.5 still requires the
complemented numeral slice equivalence, the corresponding inference natural
isomorphism, initiality of each numeral fiber and its comparison to the
per-e derivation algebra. The induced sentence-conclusion square and the
uniform Prov(e,z) presentation must then be proved. Initiality of the
whole family does not establish this fiber property. The uniform total
sentence morphism of 7.6 remains a separate obligation, including its
property at every consistent standard fiber.

Semantic K is distinct from arithmetic code models N/M. External Γ
consistency is not a PA proof of Γ consistency. The fixed universal
sentences used for 7.1 cover all elements of M≡N by elementary transfer;
this is not a claim that nonstandard codes are external finite proofs.
The proof-search lift remains partial. Exponential/parity object coding
and the uniform computation comparison are separate completed proofs.

Numerical inference realization, Miller representation independence and
cosheaf derivation initiality remain later obligations. Rows 9.1 and B.10
retain the corrected status of the completed numerical tuple comparison
in 7.7. Manuscript editing belongs to the manuscript chat; this proof
batch preserves its integrated target.
