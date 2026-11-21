# Lean proofs for manuscript v66

*Logical consequence and essential incompleteness in recursion categories*, Florian Lengyel, 18 November 2026. [Manuscript](../manuscript/logical_consequence_and_essential_incompleteness_v66.pdf)

The tables cover the 77 numbered results and three numbered definitions. Each result number links to its entry in the full correspondence, with its hypotheses, auxiliary declarations and comparisons between presentations. The links in the second column open the Lean source at the declaration. Links labelled “statement check” show the type against which the proof was checked.

## Section 3. Diagonal comparison and complementary conditionals

| Manuscript | Lean declarations |
|---|---|
| [Theorem 3.1](../FORMALIZATION_STATUS_V66.md?plain=1#L24) · Diagonal comparison | [comparison_zero_inverse_images](../Lean/CategoricalEssentialIncompleteness/V46Comparison.lean#L35) · [comparison_noncoverage](../Lean/CategoricalEssentialIncompleteness/V46Comparison.lean#L94) |
| [Corollary 3.2](../FORMALIZATION_STATUS_V66.md?plain=1#L25) · Obstruction to a lifted separator | [no_lifted_complementary_separator](../Lean/CategoricalEssentialIncompleteness/V46Comparison.lean#L112) |
| [Corollary 3.3](../FORMALIZATION_STATUS_V66.md?plain=1#L26) · Inseparability of the source pair | [source_inseparable_of_complementary_conditionals](../Lean/CategoricalEssentialIncompleteness/V46Comparison.lean#L132) |
| [Proposition 3.4](../FORMALIZATION_STATUS_V66.md?plain=1#L27) · Conditional morphisms from disjoint joins | [complementary_conditional_of_disjoint_joins](../Lean/CategoricalEssentialIncompleteness/V46Comparison.lean#L183) · [disjoint_joins_switch](../Lean/CategoricalEssentialIncompleteness/DisjointJoins.lean#L44) |

## Section 4. Internal theories and essential incompleteness

| Manuscript | Lean declarations |
|---|---|
| [Proposition 4.1](../FORMALIZATION_STATUS_V66.md?plain=1#L33) · Interpretation of a sentence theory | [interpreted_theory_equations](../Lean/CategoricalEssentialIncompleteness/V46LogicalComparison.lean#L92) · [interpreted_theory](../Lean/CategoricalEssentialIncompleteness/V46PartialMapTheory.lean#L136) |
| [Theorem 4.2](../FORMALIZATION_STATUS_V66.md?plain=1#L34) · Incompleteness under interpretation | [logical_comparison](../Lean/CategoricalEssentialIncompleteness/V46LogicalComparison.lean#L185) · [logical_comparison_target](../Lean/CategoricalEssentialIncompleteness/V46LogicalComparison.lean#L135) |
| [Corollary 4.3](../FORMALIZATION_STATUS_V66.md?plain=1#L35) · Total reductions preserve inseparability | [domain_incompleteness](../Lean/CategoricalEssentialIncompleteness/RestrictionIdempotents.lean#L222) |
| [Theorem 4.4](../FORMALIZATION_STATUS_V66.md?plain=1#L37) · Generation of sentence theories | [adjunction](../Lean/CategoricalEssentialIncompleteness/V46FirstOrderReflection.lean#L126) · [presentationAdjunction](../Lean/CategoricalEssentialIncompleteness/V46FirstOrderReflection.lean#L181) |
| [Theorem 4.5](../FORMALIZATION_STATUS_V66.md?plain=1#L38) · Translation of theories | [Translation.adjunction](../Lean/CategoricalEssentialIncompleteness/V46TranslationGalois.lean#L95) · [generation_functor_identity](../Lean/CategoricalEssentialIncompleteness/V46TranslationGalois.lean#L115) · [Axioms.adjunction](../Lean/CategoricalEssentialIncompleteness/V46FirstOrderTranslationReflection.lean#L144) |
| [Proposition 4.6](../FORMALIZATION_STATUS_V66.md?plain=1#L39) · Comparison of deduction | [generation_square](../Lean/CategoricalEssentialIncompleteness/V46DeductionComparison.lean#L130) · [inclusionComparison](../Lean/CategoricalEssentialIncompleteness/V46DeductionComparison.lean#L146) · [restrictedAdjunction](../Lean/CategoricalEssentialIncompleteness/V46DeductionComparison.lean#L176) |
| [Theorem 4.7](../FORMALIZATION_STATUS_V66.md?plain=1#L40) · Free first-order adjunction | [adjunction](../Lean/CategoricalEssentialIncompleteness/V46SignedFirstOrderAdjunction.lean#L58) · [unit_arrow](../Lean/CategoricalEssentialIncompleteness/V46SignedFirstOrderAdjunction.lean#L84) · [counit_translation](../Lean/CategoricalEssentialIncompleteness/V46SignedFirstOrderAdjunction.lean#L89) · [statement check](../Lean/CategoricalEssentialIncompleteness/V46SignedFirstOrderAdjunctionChecks.lean#L25) |
| [Corollary 4.8](../FORMALIZATION_STATUS_V66.md?plain=1#L41) · Essential incompleteness and inseparability | [essential_incomplete_iff_inseparable](../Lean/CategoricalEssentialIncompleteness/V46SignedFirstOrderIncompleteness.lean#L29) · [booleanTheory_extends](../Lean/CategoricalEssentialIncompleteness/V46SignedBooleanExtension.lean#L70) · [statement check](../Lean/CategoricalEssentialIncompleteness/V46SignedFirstOrderIncompletenessChecks.lean#L24) |

## Section 5. Theory extensions and recursion categories

| Manuscript | Lean declarations |
|---|---|
| [Lemma 5.1](../FORMALIZATION_STATUS_V66.md?plain=1#L47) · Turing structure in partial slices | [SplitTuring.turing_object](../Lean/CategoricalEssentialIncompleteness/V46SplitTuring.lean#L153) · [SplitSliceTuring.turing_object](../Lean/CategoricalEssentialIncompleteness/V46SplitSliceTuring.lean#L44) · [splittingEquivalence](../Lean/CategoricalEssentialIncompleteness/V46ConstantSlice.lean#L152) |
| [Theorem 5.2](../FORMALIZATION_STATUS_V66.md?plain=1#L48) · Theory extension and change of slice | [postcompose_full](../Lean/CategoricalEssentialIncompleteness/V46PartialSliceChangeBase.lean#L95) · [leftAdjunction](../Lean/CategoricalEssentialIncompleteness/V46PartialSliceAdjunctions.lean#L67) · [rightAdjunction](../Lean/CategoricalEssentialIncompleteness/V46PartialSliceAdjunctions.lean#L115) |
| [Theorem 5.3](../FORMALIZATION_STATUS_V66.md?plain=1#L49) · Essential incompleteness in the slice | [AssociatedCategory.associated_incompleteness](../Lean/CategoricalEssentialIncompleteness/V46AssociatedIncompleteness.lean#L57) · [associated_reduction](../Lean/CategoricalEssentialIncompleteness/V46AssociatedIncompleteness.lean#L77) · [PropositionalAssociatedIncompleteness.associated_incompleteness](../Lean/CategoricalEssentialIncompleteness/V46PropositionalAssociatedIncompleteness.lean#L90) · [statement check](../Lean/CategoricalEssentialIncompleteness/V46AssociatedIncompletenessChecks.lean#L39) |

## Section 6. The syntactic recursion category

| Manuscript | Lean declarations |
|---|---|
| [Lemma 6.1](../FORMALIZATION_STATUS_V66.md?plain=1#L55) · Arithmetized evaluation | [arithmetized_evaluation](../Lean/CategoricalEssentialIncompleteness/V46UniformTraceArithmetic.lean#L23) |
| [Lemma 6.2](../FORMALIZATION_STATUS_V66.md?plain=1#L56) · Functional search | [functional_search](../Lean/CategoricalEssentialIncompleteness/V46SyntacticSearch.lean#L114) · [search_domain](../Lean/CategoricalEssentialIncompleteness/V46SyntacticSearch.lean#L87) |
| [Lemma 6.3](../FORMALIZATION_STATUS_V66.md?plain=1#L57) · The total splitting of the syntactic category | [predicateEquivalence](../Lean/CategoricalEssentialIncompleteness/V46SyntacticPredicates.lean#L631) · [totalSplitRegular](../Lean/CategoricalEssentialIncompleteness/V46SyntacticPredicatesRegular.lean#L109) · [totalSplit_mono_partial_inverse](../Lean/CategoricalEssentialIncompleteness/V46SyntacticPredicatesImages.lean#L378) |
| [Lemma 6.4](../FORMALIZATION_STATUS_V66.md?plain=1#L58) · Finite witnesses and primitive-recursive tags | [finite_membership_PA](../Lean/CategoricalEssentialIncompleteness/V46FiniteSigmaOne.lean#L171) · [natPrimrec_representation](../Lean/CategoricalEssentialIncompleteness/V46PrimitiveRecursiveTags.lean#L338) · [selected_membership_PA](../Lean/CategoricalEssentialIncompleteness/V46PrimitiveRecursiveTags.lean#L434) |
| [Proposition 6.5](../FORMALIZATION_STATUS_V66.md?plain=1#L59) · Syntactic formula and term algebras | [categoricalSyntax](../Lean/CategoricalEssentialIncompleteness/V46SyntacticSyntaxInitial.lean#L41) · [totalCategoricalSyntax](../Lean/CategoricalEssentialIncompleteness/V46SyntacticSyntaxTotal.lean#L54) |
| [Proposition 6.6](../FORMALIZATION_STATUS_V66.md?plain=1#L60) · Syntactic list algebras | [stableListAlgebra](../Lean/CategoricalEssentialIncompleteness/V46SyntacticListsStable.lean#L25) · [totalStableListAlgebra](../Lean/CategoricalEssentialIncompleteness/V46SyntacticListsTotal.lean#L26) |
| [Proposition 6.7](../FORMALIZATION_STATUS_V66.md?plain=1#L61) · Named-variable substitution | [computedSubstitutionHom](../Lean/CategoricalEssentialIncompleteness/V46ConcreteNamedComparisonSubstitutionHom.lean#L61) · [plain_admissible_model_iff](../Lean/CategoricalEssentialIncompleteness/V46ConcreteNamedComparisonPlainAdmissibleValues.lean#L74) · [admissibleIso_result](../Lean/CategoricalEssentialIncompleteness/V46SyntacticSyntaxSubstitutionComparisonTotal.lean#L67) |
| [Lemma 6.8](../FORMALIZATION_STATUS_V66.md?plain=1#L62) · Initial derivation algebras | [derivationInitial](../Lean/CategoricalEssentialIncompleteness/V46SyntacticDerivationInitial.lean#L62) · [totalDerivationInitial](../Lean/CategoricalEssentialIncompleteness/V46SyntacticDerivationTotal.lean#L79) |
| [Theorem 6.9](../FORMALIZATION_STATUS_V66.md?plain=1#L63) · Generated syntactic sentence theories | [generated_theory](../Lean/CategoricalEssentialIncompleteness/V46SyntacticGeneratedTheory.lean#L61) · [sentenceConclusion_range](../Lean/CategoricalEssentialIncompleteness/V46SyntacticGeneratedTheory.lean#L183) |

## Section 7. Interpretation and soundness

| Manuscript | Lean declarations |
|---|---|
| [Proposition 7.1](../FORMALIZATION_STATUS_V66.md?plain=1#L69) · Interpretation in a model | [modelRangeFunctor](../Lean/CategoricalEssentialIncompleteness/SyntacticPreservation.lean#L127) · [model_map_product](../Lean/CategoricalEssentialIncompleteness/SyntacticPreservation.lean#L134) |
| [Lemma 7.2](../FORMALIZATION_STATUS_V66.md?plain=1#L70) · Finite switches | [syntactic_finite_switch](../Lean/CategoricalEssentialIncompleteness/SyntacticFiniteSwitch.lean#L213) · [image_switch_eq](../Lean/CategoricalEssentialIncompleteness/DisjointJoins.lean#L85) |
| [Corollary 7.3](../FORMALIZATION_STATUS_V66.md?plain=1#L71) · Inseparability of the syntactic pair | [syntactic_pair_inseparable_v46_of_model](../Lean/CategoricalEssentialIncompleteness/V46SyntacticComparison.lean#L32) · [syntactic_fixed_pair_inseparable_v46](../Lean/CategoricalEssentialIncompleteness/V46SyntacticComparison.lean#L59) |
| [Proposition 7.4](../FORMALIZATION_STATUS_V66.md?plain=1#L72) · Regularity of predicate interpretation | [regular](../Lean/CategoricalEssentialIncompleteness/V46PredicateInterpretationRegular.lean#L221) · [recursiveDomainComparison](../Lean/CategoricalEssentialIncompleteness/V46RecursiveDomainInterpretation.lean#L70) |
| [Lemma 7.5](../FORMALIZATION_STATUS_V66.md?plain=1#L73) · Substitution under interpretation | [evaluate_termSubstitution](../Lean/CategoricalEssentialIncompleteness/V46NamedPlainSubstitutionSemantics.lean#L38) · [holds_formulaSubstitution](../Lean/CategoricalEssentialIncompleteness/V46NamedPlainSubstitutionSemantics.lean#L55) |
| [Proposition 7.6](../FORMALIZATION_STATUS_V66.md?plain=1#L74) · Soundness of the generated theory | [exists_unique_soundnessFactor](../Lean/CategoricalEssentialIncompleteness/V46NamedPlainSoundness.lean#L91) · [sentenceConclusion_range_consistent](../Lean/CategoricalEssentialIncompleteness/V46NamedPlainSoundness.lean#L102) |
| [Lemma 7.7](../FORMALIZATION_STATUS_V66.md?plain=1#L75) · Ultrapowers and regular images | [regular](../Lean/CategoricalEssentialIncompleteness/V46Ultrapower.lean#L301) · [regularImageIso_hom_ι](../Lean/CategoricalEssentialIncompleteness/V46Ultrapower.lean#L294) |
| [Lemma 7.8](../FORMALIZATION_STATUS_V66.md?plain=1#L76) · Arithmetic ultrapower comparison | [canonicalComparison](../Lean/CategoricalEssentialIncompleteness/V46UltrapowerComparison.lean#L94) · [recursiveComparison](../Lean/CategoricalEssentialIncompleteness/V46RecursiveUltrapowerComparison.lean#L25) |
| [Theorem 7.9](../FORMALIZATION_STATUS_V66.md?plain=1#L77) · Soundness under the ultrapower comparison | [canonical_ultrapower_soundness](../Lean/CategoricalEssentialIncompleteness/V46NamedPlainUltrapowerSoundness.lean#L106) · [canonical_ultrapower_conclusion_consistent](../Lean/CategoricalEssentialIncompleteness/V46NamedPlainUltrapowerSoundness.lean#L131) |

## Section 8. Essential incompleteness of arithmetic

| Manuscript | Lean declarations |
|---|---|
| [Lemma 8.1](../FORMALIZATION_STATUS_V66.md?plain=1#L83) · Representation of the diagonal pair | [printed_representation](../Lean/CategoricalEssentialIncompleteness/V46ArithmeticDiagonalRepresentation.lean#L134) |
| [Lemma 8.2](../FORMALIZATION_STATUS_V66.md?plain=1#L84) · Partial proof search | [printed_diagonal_partial_proof_search](../Lean/CategoricalEssentialIncompleteness/V46NamedArithmeticProofSearchPrinted.lean#L107) · [ell_source_fibers](../Lean/CategoricalEssentialIncompleteness/V46NamedArithmeticProofSearchSource.lean#L130) |
| [Theorem 8.3](../FORMALIZATION_STATUS_V66.md?plain=1#L85) · Internal arithmetic comparison | [internal_comparison](../Lean/CategoricalEssentialIncompleteness/V46ArithmeticInternalComparison.lean#L249) · [total_undecidable_family](../Lean/CategoricalEssentialIncompleteness/V46ArithmeticInternalComparison.lean#L198) |
| [Corollary 8.4](../FORMALIZATION_STATUS_V66.md?plain=1#L86) · Recursive inseparability of proofs and refutations | [recursively_inseparable](../Lean/CategoricalEssentialIncompleteness/V46ArithmeticSentenceInseparability.lean#L84) · [enumeration_extension_incomplete](../Lean/CategoricalEssentialIncompleteness/V46ArithmeticSentenceInseparability.lean#L236) |
| [Proposition 8.5](../FORMALIZATION_STATUS_V66.md?plain=1#L87) · Fibers of the indexed arithmetic family | [sentenceTheory_fiber](../Lean/CategoricalEssentialIncompleteness/V46ArithmeticIndexedFibers.lean#L189) · [fiberInitial](../Lean/CategoricalEssentialIncompleteness/V46ArithmeticIndexedPrintedFamily.lean#L228) |
| [Theorem 8.6](../FORMALIZATION_STATUS_V66.md?plain=1#L88) · Uniform independent sentences | [uniform_independent_sentences](../Lean/CategoricalEssentialIncompleteness/V46ArithmeticUniformIndependent.lean#L204) · [uniform_independent_sentence_codes](../Lean/CategoricalEssentialIncompleteness/V46ArithmeticUniformIndependent.lean#L170) · [statement check](../Lean/CategoricalEssentialIncompleteness/V46ArithmeticUniformIndependentChecks.lean#L22) |
| [Proposition 8.7](../FORMALIZATION_STATUS_V66.md?plain=1#L89) · The numerical category | [equivalence](../Lean/CategoricalEssentialIncompleteness/V46NumericalTuples.lean#L417) · [partialMapEquivalence](../Lean/CategoricalEssentialIncompleteness/V46NumericalTuplesPartialMaps.lean#L36) |
| [Proposition 8.8](../FORMALIZATION_STATUS_V66.md?plain=1#L90) · Syntax and deduction in the numerical category | [firstOrder_realization](../Lean/CategoricalEssentialIncompleteness/V46NumericalRealization.lean#L55) · [canonicalRho](../Lean/CategoricalEssentialIncompleteness/V46NumericalArithmeticProofComparison.lean#L166) |
| [Lemma 8.9](../FORMALIZATION_STATUS_V66.md?plain=1#L92) · Arithmetic theory of the signed diagonal pair | [printed_statement](../Lean/CategoricalEssentialIncompleteness/V46ArithmeticSignedTheory.lean#L32) · [presentation_generation](../Lean/CategoricalEssentialIncompleteness/V46ArithmeticSignedTheory.lean#L47) |
| [Corollary 8.10](../FORMALIZATION_STATUS_V66.md?plain=1#L93) · Associated categories for the arithmetic theory | [printed_statement](../Lean/CategoricalEssentialIncompleteness/V46ArithmeticAssociatedCategories.lean#L98) |

## Section 9. Miller sequences and essential incompleteness

| Manuscript | Lean declarations |
|---|---|
| [Lemma 9.1](../FORMALIZATION_STATUS_V66.md?plain=1#L99) · Uniform computation from representations | [printed_unanimity](../Lean/CategoricalEssentialIncompleteness/V46MillerUnanimity.lean#L83) · [representations_isCompact](../Lean/CategoricalEssentialIncompleteness/V46MillerBinaryCore.lean#L127) |
| [Proposition 9.2](../FORMALIZATION_STATUS_V66.md?plain=1#L100) · The recursion category of a Miller sequence | [recursionCategory](../Lean/CategoricalEssentialIncompleteness/V46MillerCategoryTuring.lean#L80) · [relative_morphism_iff](../Lean/CategoricalEssentialIncompleteness/V46MillerCategoryRelative.lean#L129) |
| [Lemma 9.3](../FORMALIZATION_STATUS_V66.md?plain=1#L101) · Reduction to the two cuts | [printed_cut_reduction](../Lean/CategoricalEssentialIncompleteness/V46MillerCutReduction.lean#L85) |
| [Corollary 9.4](../FORMALIZATION_STATUS_V66.md?plain=1#L102) · Inseparability of the cuts | [printed_cut_inseparability](../Lean/CategoricalEssentialIncompleteness/V46MillerCutApplications.lean#L43) · [printed_cut_contrast](../Lean/CategoricalEssentialIncompleteness/V46MillerCutApplications.lean#L59) |
| [Proposition 9.5](../FORMALIZATION_STATUS_V66.md?plain=1#L103) · Splitting, syntax and derivations for a Miller sequence | [partialMapEquivalence](../Lean/CategoricalEssentialIncompleteness/V46MillerTotalPartialMaps.lean#L26) · [canonicalCategoricalSyntax](../Lean/CategoricalEssentialIncompleteness/V46MillerSyntaxTotal.lean#L85) · [proofInitial](../Lean/CategoricalEssentialIncompleteness/V46MillerFirstOrder.lean#L41) |
| [Lemma 9.6](../FORMALIZATION_STATUS_V66.md?plain=1#L104) · Deduction with parameters | [printedStatement](../Lean/CategoricalEssentialIncompleteness/V46MillerParameterizedDeduction.lean#L145) |
| [Theorem 9.7](../FORMALIZATION_STATUS_V66.md?plain=1#L105) · Incompleteness of the ordered-field theory | [printed_categorical_incompleteness](../Lean/CategoricalEssentialIncompleteness/V46MillerCanonicalAxiomIncompleteness.lean#L315) · [printed_native_incomplete_of_consistent](../Lean/CategoricalEssentialIncompleteness/V46MillerCanonicalAxiomIncompleteness.lean#L335) · [statement check](../Lean/CategoricalEssentialIncompleteness/V46MillerCanonicalAxiomIncompletenessChecks.lean#L148) |
| [Corollary 9.8](../FORMALIZATION_STATUS_V66.md?plain=1#L107) · Associated categories for the Miller theory | [printed_statement](../Lean/CategoricalEssentialIncompleteness/V46MillerAssociatedCategories.lean#L79) |

## Section 10. A recursion category from a three-point space

| Manuscript | Lean declarations |
|---|---|
| [Proposition 10.1](../FORMALIZATION_STATUS_V66.md?plain=1#L113) · Evaluation at the two endpoints | [evaluationRangeFunctor](../Lean/CategoricalEssentialIncompleteness/EffectiveForkEvaluation.lean#L35) · [left_evaluation_turing](../Lean/CategoricalEssentialIncompleteness/EffectiveForkEvaluation.lean#L103) · [right_evaluation_turing](../Lean/CategoricalEssentialIncompleteness/EffectiveForkEvaluation.lean#L106) |
| [Proposition 10.2](../FORMALIZATION_STATUS_V66.md?plain=1#L114) · The propositional syntax algebra | [syntaxAlgebra_isInitial](../Lean/CategoricalEssentialIncompleteness/ForkSyntaxInitialAlgebra.lean#L63) |
| [Proposition 10.3](../FORMALIZATION_STATUS_V66.md?plain=1#L115) · Initial derivation algebras for the fork | [printedInitial](../Lean/CategoricalEssentialIncompleteness/V46ForkDerivationInitial.lean#L141) · [shapedInitial](../Lean/CategoricalEssentialIncompleteness/V46ForkDerivationDiagram.lean#L365) |
| [Theorem 10.4](../FORMALIZATION_STATUS_V66.md?plain=1#L116) · Least theorem image in the fork | [theoremSubobject_isLeast](../Lean/CategoricalEssentialIncompleteness/V46ForkDerivationImages.lean#L112) · [theoremRange_eq_t0](../Lean/CategoricalEssentialIncompleteness/V46ForkDerivationImages.lean#L49) |
| [Theorem 10.5](../FORMALIZATION_STATUS_V66.md?plain=1#L117) · Endpoint observation and incompleteness | [cosheaf_observation_v46](../Lean/CategoricalEssentialIncompleteness/V46Applications.lean#L123) · [endpoint_theory_incomplete](../Lean/CategoricalEssentialIncompleteness/V46Applications.lean#L39) |
| [Corollary 10.6](../FORMALIZATION_STATUS_V66.md?plain=1#L118) · Computably enumerable endpoint extensions | [endpoint_axiom_extension_incomplete](../Lean/CategoricalEssentialIncompleteness/V46ForkDerivationImages.lean#L249) |
| [Proposition 10.7](../FORMALIZATION_STATUS_V66.md?plain=1#L120) · Parameterized first-order syntax and deduction for the fork | [categoricalSyntax](../Lean/CategoricalEssentialIncompleteness/V46ForkCategoricalSyntax.lean#L28) · [printedStatement](../Lean/CategoricalEssentialIncompleteness/V46ForkParameterizedDeduction.lean#L95) |
| [Proposition 10.8](../FORMALIZATION_STATUS_V66.md?plain=1#L121) · The conservative first-order extension | [printed_statement](../Lean/CategoricalEssentialIncompleteness/V46ForkFirstOrderApplication.lean#L72) · [restriction_to_domain](../Lean/CategoricalEssentialIncompleteness/V46ForkConservativeRestriction.lean#L168) · [statement check](../Lean/CategoricalEssentialIncompleteness/V46ForkFirstOrderApplicationChecks.lean#L71) |
| [Corollary 10.9](../FORMALIZATION_STATUS_V66.md?plain=1#L122) · Associated categories for the fork | [printedStatement](../Lean/CategoricalEssentialIncompleteness/V46ForkAssociatedCategories.lean#L124) · [boolean_obstruction](../Lean/CategoricalEssentialIncompleteness/V46ForkAssociatedCategories.lean#L91) · [statement check](../Lean/CategoricalEssentialIncompleteness/V46ForkAssociatedCategoriesChecks.lean#L55) |

## Appendix A. Syntax and deductively closed theories

| Manuscript | Lean declarations |
|---|---|
| [Definition A.1](../FORMALIZATION_STATUS_V66.md?plain=1#L128) · Categorical syntax | [CategoricalSyntax](../Lean/CategoricalEssentialIncompleteness/V46CategoricalSyntax.lean#L161) · [DecidableVariables](../Lean/CategoricalEssentialIncompleteness/V46CategoricalSyntax.lean#L155) · [StableListAlgebra](../Lean/CategoricalEssentialIncompleteness/V46CategoricalLists.lean#L134) |
| [Definition A.2](../FORMALIZATION_STATUS_V66.md?plain=1#L129) · Free-variable lists and sentences | [occurrenceAlgebra](../Lean/CategoricalEssentialIncompleteness/V46CategoricalFreeVariables.lean#L56) · [sentenceObject](../Lean/CategoricalEssentialIncompleteness/V46CategoricalFreeVariables.lean#L95) · [sentenceNegation](../Lean/CategoricalEssentialIncompleteness/V46CategoricalFreeVariables.lean#L105) |
| [Proposition A.3](../FORMALIZATION_STATUS_V66.md?plain=1#L130) · Admissible substitution | [substitutionFold_unique](../Lean/CategoricalEssentialIncompleteness/V46CategoricalSubstitution.lean#L464) · [formulaSubstitutionOption](../Lean/CategoricalEssentialIncompleteness/V46CategoricalSubstitution.lean#L479) · [admissibility_complemented](../Lean/CategoricalEssentialIncompleteness/V46CategoricalSubstitution.lean#L531) |
| [Definition A.4](../FORMALIZATION_STATUS_V66.md?plain=1#L131) · Closure under inference | [ClosedUnder](../Lean/CategoricalEssentialIncompleteness/V46RegularImage.lean#L30) |
| [Theorem A.5](../FORMALIZATION_STATUS_V66.md?plain=1#L132) · Least theorem subobject | [least_theorem_subobject](../Lean/CategoricalEssentialIncompleteness/V46Inference.lean#L247) · [inference_preservesRegularEpis](../Lean/CategoricalEssentialIncompleteness/V46Inference.lean#L229) |
| [Theorem A.6](../FORMALIZATION_STATUS_V66.md?plain=1#L133) · Generated first-order theory | [generated_firstOrder_theory](../Lean/CategoricalEssentialIncompleteness/V46FirstOrderTheory.lean#L28) · [firstOrder_least_image](../Lean/CategoricalEssentialIncompleteness/V46FirstOrderInference.lean#L94) |
| [Lemma A.7](../FORMALIZATION_STATUS_V66.md?plain=1#L134) · Range and regular image | [range_regularImage](../Lean/CategoricalEssentialIncompleteness/V46RegularImage.lean#L119) |

## Appendix B. The three-point cosheaf construction

| Manuscript | Lean declarations |
|---|---|
| [Proposition B.1](../FORMALIZATION_STATUS_V66.md?plain=1#L140) · Cosheaves as fork diagrams | [actualCosheafEquivalence](../Lean/CategoricalEssentialIncompleteness/ForkActualCosheaves.lean#L102) |
| [Proposition B.2](../FORMALIZATION_STATUS_V66.md?plain=1#L141) · The total category of the fork | [totalEquivalence](../Lean/CategoricalEssentialIncompleteness/EffectiveForkTotal.lean#L100) · [diagramRegular](../Lean/CategoricalEssentialIncompleteness/V46NumericalForkPartialMaps.lean#L34) |
| [Proposition B.3](../FORMALIZATION_STATUS_V66.md?plain=1#L142) · Partial maps, ranges and pullbacks in the fork | [equivalence](../Lean/CategoricalEssentialIncompleteness/V46ForkRangeStability.lean#L32) · [span_pullback_range](../Lean/CategoricalEssentialIncompleteness/V46NumericalForkPartialMaps.lean#L65) |
| [Proposition B.4](../FORMALIZATION_STATUS_V66.md?plain=1#L143) · Local connectedness of the fork | [locally_connected](../Lean/CategoricalEssentialIncompleteness/EffectiveForkConstruction.lean#L21) |
| [Lemma B.5](../FORMALIZATION_STATUS_V66.md?plain=1#L144) · Dominance | [dominance](../Lean/CategoricalEssentialIncompleteness/EffectiveForkEncoding.lean#L134) |
| [Lemma B.6](../FORMALIZATION_STATUS_V66.md?plain=1#L145) · Product, coproduct and word frames | [productFrame](../Lean/CategoricalEssentialIncompleteness/EffectiveForkProductFrame.lean#L152) · [coproductFrame](../Lean/CategoricalEssentialIncompleteness/EffectiveForkCoproductFrame.lean#L130) · [wordFrame](../Lean/CategoricalEssentialIncompleteness/EffectiveForkWordFrame.lean#L147) |
| [Theorem B.7](../FORMALIZATION_STATUS_V66.md?plain=1#L146) · Turing morphism of the fork | [tau_isTuring](../Lean/CategoricalEssentialIncompleteness/EffectiveForkTuring.lean#L158) · [tau_parameterization](../Lean/CategoricalEssentialIncompleteness/EffectiveForkTuring.lean#L152) |
| [Proposition B.8](../FORMALIZATION_STATUS_V66.md?plain=1#L147) · The fork recursion category | [recursionCategory](../Lean/CategoricalEssentialIncompleteness/EffectiveForkRecursion.lean#L231) · [splittingEquivalence](../Lean/CategoricalEssentialIncompleteness/EffectiveForkSplitEquivalence.lean#L149) |
| [Corollary B.9](../FORMALIZATION_STATUS_V66.md?plain=1#L148) · Splitting idempotents in the fork | [idempotent_splits_through_range](../Lean/CategoricalEssentialIncompleteness/V46Karoubi.lean#L29) · [karoubiEquivalence](../Lean/CategoricalEssentialIncompleteness/V46Karoubi.lean#L126) |
| [Proposition B.10](../FORMALIZATION_STATUS_V66.md?plain=1#L149) · Distinction from partial recursive functions | [fork_not_restriction_equivalent](../Lean/CategoricalEssentialIncompleteness/ForkNonEquivalence.lean#L26) · [universal_no_decidable_equality](../Lean/CategoricalEssentialIncompleteness/EffectiveForkUniversal.lean#L100) |

## Appendix C. Necessity of section lifting for inseparability

| Manuscript | Lean declarations |
|---|---|
| [Proposition C.1](../FORMALIZATION_STATUS_V66.md?plain=1#L155) · Failure of the lifting condition | [missing_lift](../Lean/CategoricalEssentialIncompleteness/OracleMissingLift.lean#L243) · [total_iff_ordinary_total](../Lean/CategoricalEssentialIncompleteness/OracleRestrictedTotal.lean#L61) |

## Appendix D. Faithful model interpretations and theory extension

| Manuscript | Lean declarations |
|---|---|
| [Theorem D.1](../FORMALIZATION_STATUS_V66.md?plain=1#L161) · Faithful family of interpretations | [family_faithful](../Lean/CategoricalEssentialIncompleteness/SyntacticFamily.lean#L43) · [familyRangeFunctor](../Lean/CategoricalEssentialIncompleteness/SyntacticFamily.lean#L53) |
| [Corollary D.2](../FORMALIZATION_STATUS_V66.md?plain=1#L162) · Inseparability under syntactic extension | [extension_arbitrary_pair_inseparable_v46](../Lean/CategoricalEssentialIncompleteness/V46SyntacticExtension.lean#L78) · [map_isTuringMorphism](../Lean/CategoricalEssentialIncompleteness/V46SyntacticExtension.lean#L41) |

[Full theorem-by-theorem correspondence](../FORMALIZATION_STATUS_V66.md) · [Verification record](../docs/V62_FULL_VERIFICATION_2026-11-17.md)
