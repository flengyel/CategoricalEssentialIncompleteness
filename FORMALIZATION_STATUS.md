# Formalization status: local-connectedness manuscript, version 5

The current target is `manuscript/essential_incompleteness_via_local_connectedness_v5.tex`,
reviewed baseline `883f1f792a5e4a244974d00458e8a9dee61b2f94`.
The full paper is **unfinished**. The earlier version-16 development is retained
below as a historical record and does not determine completion of version 5.
The author's announced title change does not change the mathematical target;
this work does not edit the manuscript.

The abstract categorical chain is proved. In particular, the combined theorem
constructs its inseparable pair using source Turing universality and target local
connectedness with section lifting, then applies the domain incompleteness
corollary. Its source total inverse-image join preservation is explicit.
Theorem 6.3 has both a generalized statement and an export with the manuscript's
prodominical and isotypical source hypotheses. No faithfulness, product preservation,
totality reflection, or totality of the source lifts is assumed there.

The category of arbitrary partial functions is constructed using `Part` rather
than decidable domains. The uniform syntactic category already present in
`FailureOfComposition.TypedProgramCategory` is reused with explicit comparisons.
Its model interpretation preserves restrictions, ranges, zeros and the canonical
binary coproduct comparison. Product preservation includes simultaneous definedness
and the canonical coding isomorphism. `codingEquiv` and `modelComparison` explicitly
compare coded carriers with recursively interpreted formal types. Interpretation
in all models is jointly faithful,
and this proves stability of syntactic idempotent joins under arbitrary inverse
image. The new `SyntacticModel.syntactic_inseparable` derives its actual syntactic
pair by Theorem 6.3 for every consistent extension of PA. Its sufficient lifting
argument uses the previously constructed, PA-verified fair preimage search in
`FailureOfComposition.TypedChoice`. It is separate from the manuscript's specified
finite two-test switching construction, which is still required.

All new names below have prefix
`CategoricalEssentialIncompleteness.LocalConnectedness.` unless stated otherwise.
“Partial” means that the row does not yet implement the entire numbered result.

| Manuscript label | Lean declarations | Hypotheses and status |
| --- | --- | --- |
| `prop:model` | `SyntacticModel.rangeFunctor`, `SyntacticModel.modelFunctor`, `SyntacticModel.modelComparison`, `SyntacticModel.codingEquiv`, `SyntacticModel.map_restriction_product`, `SyntacticModel.map_first_projection`, `SyntacticModel.map_second_projection` | **Partial.** Full-carrier semantics, uniform quotient, restrictions, ranges, zeros, canonical coproducts, product graph/preservation and recursive type comparison proved. These preservation assertions are exported for the coded functor; their transport to `modelFunctor` is not yet packaged as a single formal preservation result. |
| `thm:faithful` | `SyntacticModel.joint_faithful`; `PartialFunctions` | **Partial.** Joint faithfulness for all arithmetic models and all required properties of the single partial-function category are proved. The exact family indexed by all structures on carrier ℕ and its structure instances remain. |
| `lem:connected-alternative` | `connected_alternative` | **Proved.** Restriction zeros, restriction coproducts, and arbitrary inverse-image preservation of binary joins; the test arrow is total. |
| `prop:local-switch` | `local_switch`, `complementary_switch` | **Proved.** Split locally connected restriction category with ranges, restriction zeros, restriction coproducts, weak choice and arbitrary join inverse images. Arbitrary partial test arrows are handled by splitting their common composite restriction. |
| `thm:local-lifting` | `range_functor_lifting`; generalized `local_lifting` | **Proved.** The exact diagonal pair, canonical coproduct comparison, nonzero image identity and source-pair-specific partial lifts are used. The total parameter and diagonal equation are derived in `turing_diagonal`. |
| `prop:disjoint-joins` | `disjoint_joins_switch`, `disjoint_joins_lift` | **Proved.** First clause uses only pairwise complementarity (`PairComplementary`) and disjoint arrow joins; no global idempotent-join assumption. The range-functor clause uses the target hypotheses of Proposition 6.2. |
| `lem:switch` | — | **Pending.** The exact increasing finite-bound two-test program, fixed priority and PA graph/domain proofs have not yet been instantiated. Source choice gives an independently proved sufficient lifting route. |
| `cor:pair` | `SyntacticModel.syntactic_inseparable` | **Partial.** The categorical inseparable pair is proved for consistent PA extensions, without soundness assumptions. The exact faithful-family lift remains. `SyntacticExtension.pair0_image`, `SyntacticExtension.pair1_image` and `SyntacticExtension.extension_pair_inseparable` prove the theory-extension image equations and inseparability of the images. |
| `cor:domain-incompleteness` | `domain_incompleteness` | **Proved.** Only total inverse images must preserve joins. Exactly the two base-domain inequalities, total θ and ν, extension inclusion and disjointness are assumed. |
| `cor:arithmetic` | — | **Pending.** The classical recursion-category instance and the two numeral-substitution inclusions must be connected to the newly constructed pair. Older arithmetic incompleteness results do not discharge this row. |
| `prop:endpoint` | — | **Pending.** |
| `thm:cosheaf-observation` | — | **Pending.** |
| `prop:fork-cosheaves` | — | **Pending.** |
| `prop:fork-total` | — | **Pending.** |
| `prop:fork-structure` | — | **Pending.** |
| `prop:fork-local` | — | **Pending.** |
| `lem:fork-dominance` | — | **Pending.** |
| `lem:fork-frames` | — | **Pending.** |
| `thm:fork-turing` | — | **Pending.** |
| `prop:fork-recursion` | — | **Pending.** |
| `prop:fork-distinction` | `Fork.universal_no_decidable_equality`, `Fork.terminalSupport_card` | **Partial.** The natural equality obstruction for the actual ℕ⁴/ℕ² universal fork and the five terminal-support patterns are proved. The numerical functor-category construction and non-equivalence argument remain. |
| `prop:fork-syntax-initial` | — | **Pending.** |
| `thm:fork-proof-presentation` | — | **Pending.** |
| `prop:missing-lift` | — | **Pending.** |

Unnumbered constructions already proved include restriction-idempotent order and
inverse-image calculus; ranges with agreement and derived leastness; canonical
range joins; canonical coproduct comparison and its naturality; section uniqueness;
the full restriction-splitting category and `SplitObject.inclusion_inseparable`;
`idemOrderIso`, `partialMono_iff_existing`, `section_iff_existing` and the existing
range/zero/choice comparisons; the combined
`categorical_essential_incompleteness`; and `section_lifting_of_choice`.
`SyntacticExtension.rangeFunctor` keeps every
program index fixed and preserves products, the diagonal and the chosen Turing
morphism under provability inclusion of theories.

The first missing inference in the exact Section 4 correspondence is the formal
transport of all preservation assertions from the coded range functor to the
recursively interpreted `modelFunctor` along `modelComparison`. The product and
coproduct coding comparisons are constructed. Section 5 additionally requires
the exact family indexed by arithmetic structures on ℕ. These are implementation
obligations, not confirmed defects in the manuscript. Subsequent obligations
are listed separately above; none is an axiom
or a claimed completed instance.

Independent read-only review checked elaborated types and transitive axioms of the
categorical chain, splitting, compatibility, partial-function category, model range
functor and syntactic inseparability application. It found and prompted removal
of a global-join assumption from Proposition 6.4's first clause. The resulting
proofs use only the permitted axioms. The project verifier also audits these
exports and tracks the reviewed v5 sources alongside the historical v16 sources.

---

# Formalization status: version 16

The full definability-algebra interface and its arithmetic Boolean-presentation
instance remain **unfinished**. The supporting quotient lemma is named
`EnrichedRestriction.represented_boolean_quotient_incomplete`; it takes the
restriction, predicate, and representation data that its proof needs.
The numerical recursion category and indexing equations are separately proved.
Unused hypotheses in a supporting lemma do not refute the manuscript's
mathematical program. The remaining task is to assemble its exact compatible
structures and instances, as specified in
[FORMALIZATION_REQUIREMENTS.md](FORMALIZATION_REQUIREMENTS.md).

The external diagonal theorem, its global inseparability consequence, the
Boolean-presentation lemma, and the equivalence between complete represented
extensions and represented decisions are proved. The internal factorization
`Sep → Z_U` is also proved from enriched restriction and predicate data. The
domain equalizers, totality pullbacks, internal total-arrow operations, and
restriction inverse-image action are constructed, and the proof uses the
representation section and separator equalizer.
The global total-arrow, domain, representation, and predicate comparisons are
proved. The represented-quotient lemma is stated along `J : Tot(K₀) → C`, with
restriction idempotents and a natural subobject identification. It uses
the restriction, lattice, predicate, and section data of a definability algebra;
the additional recursion and indexing data are unused. The numerical
restriction category, PER category, full faithful functor, domain/support
comparison, support subobjects, pullbacks, and c.e. joins are constructed.
The numerical separator equivalence, binary products and their preservation
by `J`, PER finite limits, regular-image factorizations, and coequalizers of
kernel pairs are proved. Regular epimorphisms are stable under pullback, giving
a regular PER category. Finite coproducts and their van Kampen property are
proved, giving finite extensivity. The numerical domain embedding is an
injective natural bounded lattice homomorphism into the full PER subobject
predicate lattices. Boolean arrows and their fibers are characterized by
total recursive functions and recursive support inclusions. These inclusions
are exactly the complemented subobjects of the equality PER on `ℕ`.
This completes `lem:integration-numerical-subobjects`. The arithmetic
incompleteness consequence is proved below; the Lindenbaum Boolean
interpretation remains incomplete. Numerical restriction products give a
prodominical `P`-category with the original restriction operation. Its domain
lattices and total-arrow category are compared explicitly with the existing
numerical constructions. All declarations below are in the namespace
`CategoricalEssentialIncompleteness`.

The numerical category is a recursion category. Computable enumeration and
counting give recursive isomorphisms with `ℕ`, and partial application of
program codes proves the full Turing factorization property. A choice of
codes supplies a set-level indexing function and its evaluation equation.
The numerical hom-objects, restriction, zeros, and products are internalized
in `Type`. Their domain equalizers and totality pullbacks are compared with
numerical domains and total arrows. The domain lattice and inverse-image
equations hold at every parameter type, and the indexing function lifts to
an internal section of evaluation.
The full PER subobject predicates and monic domain embedding are internalized.
Evaluation of global arrows identifies the partial and total categories with
their numerical counterparts.
The global predicate functor is naturally identified with the full PER
subobject functor along the product-preserving functor on global total arrows,
and the induced domain map agrees with numerical support inclusion.

Canonical sentence coding and joint numeral substitution are constructed in
Foundation's arithmetic language. The representation equations are equivalent
to strong numeralwise definability, and the internal representation projection
has a section exactly when every recursive set has such a definition. Applying
the internal diagonal theorem proves recursive inseparability of theorem and
refutation indices. The supports are c.e. when the theory is c.e.
Consequently, every consistent c.e. extension of a consistent arithmetic theory
strongly defining every recursive set is incomplete; every consistent
extension has nonrecursive theorem support. Consistent extensions of `PA⁻`
satisfy the definability hypothesis.

## Correspondence

| Manuscript label | Lean declaration or module | Status |
| --- | --- | --- |
| `eq:integration-rows` | `DiagonalData.Represents` | Both representation equations, with the same total arrow and separate objects `U`, `S`. |
| `thm:integration-diagonal` | `DiagonalData.integration_diagonal`; `restriction_integration_diagonal` | Proved. The latter uses `DomSemilattice` elements and `RestrictionCategory.TotalSubcategory`. |
| `cor:definability-algebra-inseparability` | `DiagonalData.inseparable`; `restriction_inseparable`; `InternalDiagonalData.global_inseparable` | Proved. The last declaration derives the external representation premise from the internal section. |
| Restriction-idempotent and total-arrow objects in `sec:definability-algebras` | `EnrichedRestriction.domainObject`; `totalObject`; `domainPointsEquiv`; `totalPointsEquiv` | Equalizer and pullback, with generalized-point equivalences. All four declarations are in `EnrichedRestriction`. |
| Total products and restriction inverse image in `def:generalized-definability-algebra` | `EnrichedRestriction.totalHom_cartesian`; `domainPredicates` | Internal total composition and binary products, and the internal domain-predicate action, are constructed. The latter declaration is also in `EnrichedRestriction`. |
| Global total-arrow comparison in `sec:definability-algebras` | `EnrichedRestriction.globalTotalEquivalence`; `globalTotalPreservesBinaryProducts` | Equivalence with the wide subcategory of total arrows, preserving binary products. Both names are in `EnrichedRestriction`. |
| Global domain comparison in `sec:definability-algebras` | `EnrichedRestriction.globalDomainOrderIso`; `globalDomainInverse_comparison` | Bounded lattice comparison with ordinary restriction idempotents, compatible with partial inverse image. Both names are in `EnrichedRestriction`. |
| Global representation equations | `InternalDiagonalData.global_represents_iff`; `global_representation` | Comparison through the chosen-product isomorphism and representatives obtained from the internal section. Both names are in `InternalDiagonalData`. |
| Natural global predicate identification along `J` | `SubobjectIdentification.presheafIso`; `EnrichedRestriction.domainSubobject_naturality` | Natural presheaf isomorphism and natural injective bounded lattice map from ordinary domains to subobjects. |
| `eq:v8-complement-pullback` | `InternalLattice.Complements`; `InternalLattice.liftComplement` | Pullback, universal complementary pair, and lift at every parameter constructed. |
| `eq:v8-representation-pullback`; `eq:v8-representation-section` | `InternalDiagonalData.Representation`; `representation_section_iff`; `RepresentationSection.represents` | Pullback and section; equivalence with the universal representation equations; generalized representatives derived. The latter two names are in `InternalDiagonalData`. |
| `thm:internal-inseparability` | `InternalDiagonalData.internal_inseparability`; `no_global_separator`; `separatorIsInitial` | Factorization at the `Sep` and both consequences proved over an arbitrary finitely complete base. `EnrichedRestriction.enriched_internal_inseparability` and `enriched_no_global_separator` supply the constructed domain and total-arrow data; the latter two names in this row's declaration column are in `InternalDiagonalData`. |
| `lem:complete-boolean-presentation` | `BooleanPresentation.consistent_iff_mono`; `BooleanPresentation.complete_iff_regularEpi`; `BooleanPresentation.consistent_complete_iff_isIso` | Proved in a regular extensive category, with equalizer fibers and the bound copairing. |
| `thm:categorical-essential-incompleteness` | Supporting lemmas `EnrichedRestriction.represented_boolean_quotient_incomplete`; `represented_boolean_quotient_boundCopair_not_regularEpi` | Both quotient conclusions are proved from restriction/predicate/representation hypotheses. The full definability-algebra interface and its concrete arithmetic Boolean-presentation instance remain unfinished. |
| `prop:complete-extensions-and-decisions` | `complete_extensions_and_decisions`; `EnrichedRestriction.global_complete_extensions_and_decisions` | Proved for Boolean quotients and the constructed internal Boolean algebra on `1 + 1`, including the specialization to ordinary restriction domains and the identification along `J`. |
| Boolean-homomorphism conclusion of `cor:integration-no-boolean-map` | `no_represented_boolean_decision`; `EnrichedRestriction.global_no_boolean_decision` | Proved, including the specialization along `J` from the internal section. The arbitrary-arrow clause is not claimed. |
| Numerical category and domain identification in `sec:integration-numerical` | `Numerical.numericalRestriction`; `Numerical.domainSupportOrderIso`; `Numerical.recursive_iff_complemented_support` | Extensional partial recursive arrows, restriction laws, c.e. domain lattice, partial inverse image, and recursive/complemented equivalence proved. |
| Isotype of the numerical category in `sec:integration-numerical` | `Numerical.enumerate_computable`; `rank_computable`; `natIso`; `totalNatIso`; `numericalIsotype` | Increasing enumeration and counting give inverse recursive total arrows between each numerical object and `ℕ`. Both inverse equations hold as partial maps with the required source restrictions. All names are in `Numerical`. |
| Numerical Turing morphism in `sec:integration-numerical` | `Numerical.turingEvaluator`; `codeParameter`; `turingEvaluator_parameterization`; `turingEvaluator_isTuringMorphism` | Universal partial recursive evaluation and computable partial application of program codes give the factorization for every numerical parameter object. Equality includes inputs outside the source carrier. All names are in `Numerical`. |
| Numerical recursion category and indexing in `sec:integration-numerical` | `Numerical.numericalRecursionCategory`; `turingIndexing`; `turingIndexing_evaluation` | The concrete `PRecursionCategory` instance is constructed. The indexing function assigns a total parameter arrow to each extensional partial arrow and satisfies the evaluation equation. All names are in `Numerical`. |
| Numerical enriched restriction structure in `sec:integration-numerical` | `Numerical.enrichedHom`; `enrichedRestriction`; `enrichedProducts`; `enrichedZeros` | Hom-sets and pointwise operations define the enriched restriction, zero, and product data over `Type`. All names are in `Numerical`. |
| Numerical internal domain lattices | `Numerical.enrichedDomainEquiv`; `enrichedDomainFamilyOrderIso`; `enrichedDomainInverse_apply`; `enrichedDomainLattices` | The actual equalizer is identified with numerical domains. Its bounded distributive lattice and partial inverse-image laws are constructed at every parameter type. All names are in `Numerical`. |
| Numerical internal totality and indexing | `Numerical.enrichedTotalEquiv`; `enrichedTotal_comp`; `enrichedTotal_pair`; `internalEvaluation_composition`; `internalIndexing_evaluation` | The actual totality pullback is identified with numerical total arrows, with compatible operations. Internal indexing is a section of the internal Turing evaluation morphism. All names are in `Numerical`. |
| Numerical internal predicates and embedding | `Numerical.enrichedPredicates`; `enrichedDomainSubobjectHom`; `enrichedPredicateEmbedding` | Full PER subobjects give the internal predicate objects. The actual domain equalizers embed by monic bounded lattice maps, natural for every parameter type. All names are in `Numerical`. |
| Numerical global category comparison | `Numerical.enrichedGlobalEquivalence`; `enrichedGlobalTotalEquivalence`; `globalTotalEvaluationPreservesBinaryProducts` | Evaluation and constant families give inverse equivalences of the partial and total categories. Restriction, zero, partial pairing, and projections agree; the total equivalence preserves binary products. All names are in `Numerical`. |
| Numerical global subobject identification | `Numerical.enrichedToPER`; `enrichedToPERPreservesBinaryProducts`; `enrichedPredicateSubobjectIdentification`; `enriched_domainSubobject_apply` | The PER-valued functor preserves binary products. Its full subobject functor is naturally identified with global predicates, and the enriched domain map agrees with numerical support inclusion. All names are in `Numerical`. |
| `cor:numerical-definability-algebras` | `NumericalEnriched*`; `ArithmeticSyntax.representationSection_iff_definability` | The numerical enriched structure and the section/definability equivalence are proved for arithmetic syntax with full PER predicates. The version using only domain predicates `E` is not yet assembled. |
| PER category and functor `J` in `sec:integration-numerical` | `NumericalPER.perCategory`; `Numerical.toPER`; `Numerical.toPER_full`; `Numerical.toPER_faithful` | Arbitrary PERs and arrows defined by equivalence classes of representing functions constructed. The functor is full and faithful and preserves binary products. The PER category is regular and finitely extensive. |
| Binary products and preservation by `J` in `sec:integration-numerical` | `Numerical.productIsLimit`; `Numerical.toPER_preservesBinaryProducts` | Recursive tuple coding gives infinite recursive product carriers. Projection equations for the PER comparison prove preservation. |
| Numerical restriction products in `sec:integration-numerical` | `Numerical.partialPair_fst`; `partialPair_snd`; `partialPair_proj`; `numericalPCategory`; `numericalProdominical` | Partial pairing, the restriction projection equations, all `P`-category equations, and zero absorption are proved. All names are in `Numerical`. |
| Compatibility of numerical restriction and total products | `Numerical.inducedRestriction_eq`; `pcategoryTotalEquivalence`; `fromPCategoryTotal_pairing`; `totalPair_eq_lift`; `toPER_totalPair` | The induced restriction equals the original structure. The total-arrow equivalence identifies pairings and preserves products; pairing agrees with the existing numerical and PER product constructions. All names are in `Numerical`. |
| Numerical domains in the imported domain API | `Numerical.domainOrderIso`; `numericalDomainJoins`; `domainComparisonHom`; `domainComparisonHom_inverse` | The domain presentations are bounded lattice isomorphic, with identical underlying arrows and compatible partial inverse image. Joins and their stability are constructed from the c.e. support lattice. All names are in `Numerical`. |
| Finite limits and regular images in `sec:integration-numerical` | `NumericalPER.perHasFiniteLimits`; `imageFactorisation`; `hasCoequalizer_of_isKernelPair` | Terminal object, products, equalizers, and regular-epimorphism/monomorphism factorizations are constructed. Every kernel pair has a coequalizer. The latter two declarations are in `NumericalPER`. |
| Regular PER target in `sec:integration-numerical` | `NumericalPER.pullback_isPullback`; `pullbackSnd_regularEpi`; `perRegular` | Explicit pullbacks and stability of regular epimorphisms proved, giving `Regular NumericalPER`. All names are in `NumericalPER`. |
| Extensive PER target in `sec:integration-numerical` | `NumericalPER.coproductIsColimit`; `decompositionIso`; `perFinitaryExtensive`; `coproduct_disjoint` | Finite coproducts, decomposition into inverse images, the van Kampen property, and disjointness are proved. All names are in `NumericalPER`. |
| Support order and inverse image in `lem:integration-numerical-subobjects` | `NumericalPER.supportSubobject_le_iff`; `supportSubobject_eq_iff`; `inverse_isPullback` | Subobjects and the full pullback universal property proved for arbitrary supports. All names are in `NumericalPER`. |
| C.e. joins and the image of `j` in `lem:integration-numerical-subobjects` | `NumericalPER.enumerable_union_isLUB`; `Numerical.domainSubobject`; `Numerical.supportSubobject_in_range_iff` | The union is least among all categorical upper bounds. The domain map is an order embedding whose image among support inclusions is exactly c.e. supports. |
| Predicate functors and natural bounded lattice embedding in `lem:integration-numerical-subobjects` | `subobjectPredicates`; `Numerical.domainPredicates`; `Numerical.predicates`; `Numerical.domainEmbedding`; `Numerical.predicateSubobjectIdentification` | Proved. General predicates are all PER subobjects along `J`; domain reindexing and categorical pullback agree. Bounds, meets, joins, and specified complementary pairs are preserved. |
| Boolean arrows in `lem:integration-numerical-subobjects` | `NumericalPER.booleanIso`; `booleanIso_point`; `booleanArrowEquiv` | The chosen coproduct of terminal objects is identified with `D_{0,1}`, including both points. Arrows from `D_ℕ` correspond bijectively to total recursive Boolean functions. All names are in `NumericalPER`. |
| Boolean fibers and complemented subobjects in `lem:integration-numerical-subobjects` | `NumericalPER.booleanArrow_boundFiber`; `exists_boolean_fiber_iff_recursive_support`; `isComplemented_iff_recursive_support` | Proved for all subobjects of `D_ℕ`. Boolean fibers, recursive support inclusions, and complemented subobjects coincide. All names are in `NumericalPER`. |
| Complemented domains in `lem:integration-numerical-subobjects` | `Numerical.isComplemented_iff_represented_domain`; `isComplemented_domainSubobject_iff` | Every complemented subobject of `D_ℕ` is represented by a complementary domain pair. The domain embedding preserves and reflects existence of a complement. Both names are in `Numerical`. |
| `thm:integration-essential-equivalence` (ii) | `Numerical.no_separator_iff_recursively_inseparable` | The support statement is proved for arbitrary disjoint supports, with PER subobject inequalities and numerical restriction domains. |
| Effective syntax in the strong numeralwise definability subsection | `ArithmeticSyntax.sentenceEquiv`; `computable_numeralSubstitution`; `ArithmeticSyntax.substitutionFunction_computable`; `substitutionArrow` | Computable inverse sentence coding and substitution jointly in the formula and numeral; the latter arrow is total. |
| `prop:integration-arbitrary-adequacy`; `thm:integration-essential-equivalence` (i) | `ArithmeticSyntax.recursiveSet_adequacy_iff`; `represents_all_pairs_iff`; `representationSection_iff_definability` | Proved for the arithmetic language. Consistency is the only hypothesis on the theory in these equivalences. All names are in `ArithmeticSyntax`. |
| Theorem/refutation domains for c.e. theories | `ArithmeticSyntax.theoremSupport_enumerable`; `refutationSupport_enumerable`; `theoremDomain_predicate`; `refutationDomain_predicate` | The supports are c.e. under `T.RE` alone, and their partial identities represent the stated PER predicates. |
| Inseparability under (i) in `thm:integration-essential-equivalence` | `ArithmeticSyntax.supports_recursivelyInseparable_of_definability` | Proved by applying the internal categorical diagonal theorem to the constructed representation section. |
| Arithmetic essential undecidability and incompleteness under (i) | `ArithmeticSyntax.essential_undecidability_of_definability`; `essential_incompleteness_of_definability` | Every consistent extension has nonrecursive theorem support; every consistent c.e. extension is incomplete. The original theory need not be c.e. |
| `thm:integration-essential-equivalence` (iii), Boolean-homomorphism equivalence | — | Open; requires the Lindenbaum PER and the correspondence with complete decidable consistent extensions. |
| `prop:numerical-boolean-extensions` | — | Open. |
| `cor:arithmetic-representation-incompleteness` | `ArithmeticSyntax.every_pair_represented`; `representationSection`; `supports_recursivelyInseparable`; `incomplete_of_PAminus` | Representation, the section, inseparability, and essential incompleteness are proved for consistent arithmetic-language extensions of `PA⁻`. The Lindenbaum Boolean-homomorphism conclusion and domain-predicate algebra remain open. |

## Hypotheses and constructions

`PredicateLattice` specifies bounded distributive lattices and contravariant
bounded lattice reindexing. `PredicateEmbedding` specifies injective bounded
lattice maps and their naturality. `ComplementaryPair` specifies only the two
elements under consideration; no Boolean structure is assumed on `E(X)` or
`P(X)`. The distinguished predicates are arbitrary elements of `P(S)`.

`DiagonalData.diagonal_collapse` constructs the diagonal pair by pulling back
the reversed separator pair along `delta = prod.lift id id >> s`. It uses
`row g = prod.map g id >> s` and the arrow `prod.lift id g`. The product laws
give `pairing >> row g = g >> delta`. Naturality and injectivity of `j` then
equate complementary domains, giving bottom equals top. Nontriviality is used
only to pass from this equality to the nonexistence result.

`RestrictionPredicates.lean` uses the existing `PCategory` presentation of
binary restriction products. It defines a distributive lattice from the existing domain order and
composition with the following explicit additional
structure from the manuscript:

- `DomainJoins`: joins with their least-upper-bound laws, distributivity, and
  preservation by total inverse images.
- `RestrictionZeros`: the restriction of a zero is zero. The existing
  prodominical structure implies this law, but the diagonal theorem does not
  require the stronger hypothesis as a separate premise.

The inverse image is defined as `rst (f >> e.hom)`. Its meet, bounds, identity,
and composition laws are proved. Binary products in the total-arrow category
are constructed from the existing near-product cone. No ranges, coproducts in
the restriction category, density assumption, or global complementation are
used. Identity unequal to zero implies the required lattice nontriviality.

`BooleanObject` specifies a Boolean algebra on every generalized-element
hom-set, with precomposition given by bounded lattice homomorphisms. The
representing meet, join, and complement arrows and their evaluation laws are
constructed in `BooleanQuotients.lean`; the bounds are global arrows from the
terminal object. `BooleanMorphism` is bounded-lattice-homomorphic on all these
hom-sets. `BooleanPresentation` and `BooleanQuotient` include
`IsRegularEpi` proofs, and the induced presentation is constructed.

`boundFiber` is the equalizer subobject of the presentation and the
constant bound arrow. `boundFiber_le_postcomp` proves the two inclusions used
in the quotient argument. `boolean_quotient_incomplete` assumes a regular
extensive category, an order isomorphism from `P(S)` to its relevant subobject
lattice, and the external representation data. It proves that consistent
represented quotient fibers cannot have join top. Since the external data
are already supplied, this proof only needs the identification at `S`.
`GlobalSubobjects.lean` supplies this component from the natural identification
along `J`, and `RepresentedQuotients.lean` states the conclusion using ordinary
restriction idempotents.

`BooleanPresentations.lean` proves the three clauses of
`lem:complete-boolean-presentation`. Its supporting results establish that the
image of a copairing is the join of the two images; inverse image along a
regular epimorphism reflects subobject order; and a copairing of monomorphisms
is monic exactly when the two subobjects are disjoint. The completeness proof
constructs the pullback square whose upper arrow is the copairing of the two
fiber inclusions and whose lower arrow is the bound copairing. Universal
coproducts give this square; regularity then transfers the assertion that the
relevant arrow is a regular epimorphism. No preservation-of-unions assumption
is added. The supporting comparisons apply to any two global points, and the
three principal declarations specialize them to the Boolean bounds.

`CharacteristicArrows.lean` constructs the coproduct decomposition associated
with a specified complementary pair of subobjects. Its characteristic arrow
has the negative and positive subobjects as its exact lower and upper fibers,
and is uniquely determined by them. It also proves that the two fibers of
every arrow to `1 + 1` form a colimit cofan. No subobject classifier for arbitrary
subobjects is assumed.

`TwoBoolean.lean` constructs Boolean operations as arrows on `1 + 1`.
It proves their identities by restriction to the truth-value fibers of each
generalized argument. Thus the use of finite Boolean truth tables is justified
over arbitrary source objects; global points are not assumed to detect arrow
equality. The resulting Boolean algebras on the hom-sets are natural under
precomposition. `BooleanObject.boundMorphism` proves that the canonical bound
copairing into every internal Boolean algebra is a Boolean homomorphism.

`BooleanDecisions.lean` proves both directions of
`prop:complete-extensions-and-decisions`. A consistent complete quotient has
an invertible bound copairing; composing the quotient with its Boolean inverse
produces the required decision. Conversely, every Boolean homomorphism to
`1 + 1` is a split epimorphism, so it gives a Boolean quotient. The
characteristic-arrow fiber equations identify its two represented fibers.
`PredicateEmbedding.subobjectMap` and the specialized equivalence keep the
restriction-domain sort `E(S)` distinct from the general-predicate sort `P(S)`.
The final `no_represented_boolean_decision` result combines this equivalence
with the existing external diagonal obstruction.

## Internal and global comparisons

`InternalLattices.lean` describes a bounded distributive lattice object by its
lattice structures on all generalized-element hom-sets, natural under
precomposition. It constructs the representing meet and join arrows and the
complementary-pair pullback. Its two projections are complementary,
and a complementary pair at every parameter has a lift to this pullback.

`InternalCartesian.lean` specifies hom-objects, composition, identity, and
binary-product operations as morphisms in the base. `CartesianLaws` gives the
category and binary-product equations at all parameters. `InternalPredicates`
specifies internal action arrows, bounded lattice preservation, and the
identity and contravariant composition equations. `InternalPredicateEmbedding`
has monic components; injectivity at arbitrary parameters is derived
from monicity. None of these fields assumes separator collapse or a
factorization through the bound equalizer.

`InternalDiagonalData.diagonal_collapse` proves the diagonal calculation at
any parameter object. `InternalRepresentation.lean` forms the pullback
`R`, derives `rho` from its section, and proves both representation equations
after any generalized complementary pair. It also proves the converse:
the universal representation equations construct a section of `R → C_U`.

The module forms `Sep` as the manuscript's meet-equation equalizer. Its two
projections give the complementary separator pair. The constructed map
`separatorDiagonal : Sep → C_U` is `gamma`; composition with `rho` gives the
required representative. The diagonal calculation equates bottom and top as
morphisms `Sep → E_U`, giving `separatorFactor : Sep → Z_U` and its equation.
`no_global_separator` follows from unequal global bounds. `separatorIsInitial`
proves the strict-initial-object consequence. No well-pointedness, enough
points, or inference from absence of global points to initiality is used.

The earlier `parameterized_separator_factorization` remains available, but
the new construction no longer requires its parameterized separator and
representative to be supplied separately.

`EnrichedRestriction.lean` gives the enriched restriction equations and
constructs the ordinary restriction category of generalized arrows at every
parameter. It reuses `PCats.Restriction` for the restriction calculus. The
object `domainObject X` is the fixed-point equalizer of restriction;
`totalObject X Y` is the pullback of restriction along the identity. The
proved `domainPointsEquiv` and `totalPointsEquiv` identify their generalized
points with the corresponding fixed points and total arrows.

`EnrichedTotals.lean` starts with the partial projection equations for chosen
restriction products. It derives closure of total arrows under pairing and
lifts identities, composition, projections, and pairing through the totality
pullbacks. The monic inclusions then prove `totalHom_cartesian`; its category
and product laws are conclusions, not additional hypotheses.

`EnrichedDomains.lean` constructs restriction inverse image by lifting the
restriction of composition through the domain equalizer. It proves naturality
under parameter change, the identity and composition equations, and meet
preservation. `partialDomainAction` represents this inverse image as a morphism
on `H(X,Y) × E_Y`; `domainAction` is its restriction to `T(X,Y) × E_Y`.
`Zeros` specifies the internal restriction zeros. `DomainLattices`
specifies the manuscript's bounded distributive lattice structures on the
equalizers, with meet identified with composition, bounds identified
with zero and identity, and joins stable under inverse image. The declaration
`domain_le_iff` proves that the resulting order is the restriction-domain
order. Bound preservation follows from totality and the zero equations;
it is not included in the join-stability assumption.

The constructed `domainPredicates` and `totalHom` instantiate the internal
separator proof in `enriched_internal_inseparability`. The declaration
`enriched_no_global_separator` uses inequality of the original enriched
identity and zero, via the proved `domain_bounds_ne` lemma. The construction
assumes neither a complement for every domain nor that the distinguished
predicates lie in the image of `j_S`. All operations are morphisms of the
base, with structural equations at arbitrary parameters.

`EnrichedQuotients.lean` applies this result directly to Boolean
presentations and quotients. Consistency and assumed completeness reflect
through the monic bounded lattice embedding to make the two representing
domains complementary. Bound preservation gives the separator inequalities,
and the lift to `Sep` contradicts `enriched_no_global_separator`. The equivalent
assertion that the bound copairing is not a regular epimorphism follows from
the already proved Boolean-presentation lemma. The theorem takes the
subobject identification at the sentence object explicitly; no independent
external representation operation is assumed.

`GlobalCartesian.lean` constructs the ordinary category of global arrows and
its binary product universal property. The projection and naturality equations
of `globalProductIso` compare the enriched product with Mathlib's chosen
product. Global predicates and the internal monic components give the external
predicate lattice and natural injective embedding.

`GlobalTotals.lean` takes `K₀ = Parameterized R 1` and defines `GlobalTotal`
as the wide subcategory of `RestrictionCategory.isTotal`. Its equivalence with
global total hom-objects has proved identity, composition, natural-isomorphism,
and triangle laws, and preserves binary products. Zero morphisms and the
identity/zero comparison are constructed. The imported `TotalSubcategory`
abbreviation additionally requires a `PCategory` presentation; the new definition
uses the same wide-subcategory construction directly.

`GlobalDomains.lean` defines ordinary restriction domains by an endomorphism
and the equation `rst e = e`. The global equalizer comparison is an order
isomorphism. Its lattice order is `e >> d = e`, meet is composition, and the
bounds have underlying arrows zero and identity. The comparison commutes with
inverse image `rst (f >> e)` for partial as well as total arrows.

`GlobalRepresentation.lean` includes the chosen-product isomorphism in the
external substitution map. It proves the row comparison and the equivalence
of internal and external representation equations at the terminal object.
The internal section supplies external representatives and global inseparability.

`GlobalSubobjects.lean` reindexes predicates onto `GlobalTotal`.
`SubobjectIdentification` specifies order-isomorphism components and their
pullback naturality equation. `presheafIso` constructs the natural
isomorphism of contravariant functors; universe lifts place both in one
category of types. `domainSubobject` combines the domain comparison, internal
embedding, and subobject identification. Its bounded lattice laws, injectivity,
and naturality for subobject pullback are proved.

`RepresentedQuotients.lean` states the supporting quotient lemma with ordinary
nontriviality `1_U ≠ 0`, a regular extensive target, a
functor `J`, the natural identification, Boolean presentations and
quotients, and representing ordinary restriction idempotents. It proves
incompleteness and the bound-copairing conclusion. It also specializes the
decision equivalence and excludes represented Boolean decisions.

The precise input scope is the restriction, product, zero, lattice, predicate,
and representation-section part of Definition `def:generalized-definability-algebra`.
The proof does not use the additional recursion-category or indexing data.
The quotient argument needs only the identification component at `S`;
product preservation by `J` is not a hypothesis of this supporting lemma.
No additional mathematical hypothesis is introduced by the global comparison.
A single Lean record for the entire definability algebra, including its
recursion and indexing data, and a comparison with Mathlib's bundled enriched
category interface are not provided.

## Numerical constructions

`NumericalCategory.lean` uses the manuscript's infinite recursive subsets of
`ℕ` as objects. An arrow is a Mathlib partial recursive function on `ℕ`, with
domain contained in the source and values in the target. Equality is equality
of partial functions. Composition uses partial bind; restriction is partial
identity on the domain. The category and four restriction laws, zero morphisms,
totality characterization, and nontriviality at `ℕ` are proved.

`NumericalDomains.lean` identifies restriction idempotents with c.e.
subsets of the source by an order isomorphism. The bounded distributive lattice
has intersection and union as operations; its order agrees with restriction
composition, and its bounds have arrows zero and identity. Partial inverse
image has the support `∃ m ∈ f(n), m ∈ A`. Post's theorem supplies the recursive
decision procedure from complementary c.e. supports. Conversely a recursive
set and its complement give complementary restriction idempotents.

`NumericalPER.lean` constructs arbitrary symmetric transitive relations on
`ℕ` and their category. A representing function is partial recursive, defined on every
supported input, and respects the two relations. Arrow equality is target
relatedness of the outputs at every supported input. The equivalence of representing functions,
compatibility of composition, and category laws are proved. Neither the PER
relation nor its support is assumed c.e.

`NumericalEmbedding.lean` defines `J` on the wide subcategory of total
numerical arrows. It preserves identities and composition and is full and
faithful. The fullness proof restricts a representing function to the recursive source,
giving a partial map undefined elsewhere. Total arrows on `ℕ` are also compared
in both directions with ordinary total recursive functions.

`NumericalSubobjects.lean` constructs the monomorphism `D_A → D_X` for
every inclusion `A ⊆ X`, and proves that its subobject order is precisely
support inclusion. The inverse-image square has a universal lift for arbitrary
PER sources and a uniqueness proof. Its support agrees with the numerical
restriction inverse image along total arrows. `domainSubobject` is an order
embedding, and a support inclusion belongs to its image exactly when its
support is c.e.

`NumericalUnions.lean` dovetails the two c.e. support tests using Mathlib's
partial-recursive merge construction. This supplies a factorization through
every common categorical upper bound, proving that the support union is the
join among all PER subobjects. The conclusion is restricted to c.e. supports;
arbitrary support inclusions are not identified with the full subobject lattice.

`NumericalSupportLattice.lean` identifies full and empty support inclusions
with the top and bottom subobjects, and intersections with categorical meets.
For two c.e. supports, the preceding least-upper-bound theorem identifies their
union with the categorical join.

`NumericalDomainReindexing.lean` proves that restriction inverse image preserves
bottom, meets, and joins along partial numerical arrows. It preserves top along
total arrows. Identity and composition laws make these bounded lattice maps
contravariant on the total-arrow category.

`NumericalDomainEmbedding.lean` proves preservation of the two bounds, meets,
and joins, and naturality with respect to genuine categorical pullback.
Injectivity gives reflection, as well as preservation, of complementarity for
a specified pair of domains. It does not assert that all domains have complements.

`SubobjectPredicates.lean` derives a distributive lattice on all subobjects
from regularity and finite extensivity. A pullback of a regular epimorphism
followed by a monomorphism proves image stability. Finite extensivity then
gives pullback preservation of binary joins; direct image along a monomorphism
preserves joins by its adjunction with pullback. These properties prove
distributivity and supply bounded lattice reindexing.

`NumericalPredicates.lean` combines these results into the domain predicate
functor, the full PER subobject predicate functor, their natural embedding,
and the subobject identification along `toPER`. No new premise is added to
the numerical construction.

`ComplementedSubobjects.lean` proves that complemented subobjects in a
regular finitely extensive category are exactly the upper fibers of arrows
to `1 + 1`. The two point subobjects are complementary, and bounded lattice
pullback preserves their complementarity for every arrow.

`NumericalBooleanObject.lean` constructs the equality PER on `{0,1}` as a
coproduct of terminal PERs. Recursive coding and decoding give an isomorphism
with the explicit PER coproduct; the universal property identifies it with
the chosen object `Two NumericalPER`. Both point equations and their singleton
subobject equations are proved.

`NumericalBooleanArrows.lean` constructs the bijection between total recursive
Boolean functions and arrows from `D_ℕ` to this Boolean PER. A representing
partial recursive function is total on every natural number. Its supported
outputs are zero or one, giving a total recursive Boolean function. Equality
of morphism classes agrees with equality of these functions.

`NumericalBooleanFibers.lean` identifies each truth-value fiber with the
corresponding inverse-image support inclusion. These supports are recursive,
and every recursive subset occurs as the upper fiber of a Boolean arrow.

`NumericalComplementedSubobjects.lean` applies the characteristic-arrow
construction to arbitrary complemented subobjects of `D_ℕ`. The Boolean
comparison and fiber calculation identify them exactly with recursive support
inclusions. They are therefore exactly the images of complementary numerical
domain pairs. This also proves that the numerical domain embedding reflects
existence of a complement on `ℕ`.

`NumericalInseparability.lean` compares the subobject separator
inequalities with a recursive separating set. It proves the absence-of-separator
equivalence for disjoint supports without assuming that either distinguished
support is c.e. This supplies the support argument of
`thm:integration-essential-equivalence` (ii). It does not yet instantiate the
supports with arithmetic theorem and refutation sets.

`PERProducts.lean` defines the product relation using recursive tuple coding
and proves its universal property against every PER source.
`NumericalProducts.lean` proves that the corresponding numerical carrier is
recursive and infinite. The comparison isomorphism under `J` is represented by
the identity function on pair codes. Its projection equations prove that `J`
preserves binary products; full faithfulness then gives the numerical product
universal property.

`NumericalPartialProducts.lean` pairs partial numerical arrows on the
intersection of their domains. The projection equations include the
restriction of the other component. Every partial arrow into a product is
recovered from its projections, and precomposition preserves pairing.

`NumericalPCategory.lean` uses these operations to construct `PCategoryStruct`
and prove all `PCategory` equations. Recursive reassociation and transposition
of tuple codes prove the naturality of the associator and symmetry. The
derived restriction operation equals the original one, and the two
restriction structures are proved equal. Both zero-absorption laws give
`Prodominical Numerical`.

`NumericalTotalProducts.lean` proves totality of pairing of total arrows and
identifies it with the lift of the existing numerical product cone. The
functor to PERs sends this pairing to the PER pairing through `productIso`.

`NumericalTotalComparison.lean` constructs explicit mutually inverse functors
between the total-arrow categories defined using the induced and original
restrictions. The functors retain underlying arrows and identify the two
product pairings. The resulting equivalence preserves binary products.

`NumericalDomainComparison.lean` gives an order isomorphism between
`Numerical.Domain X` and `DomSemilattice X`, with identical underlying arrows.
It preserves partial inverse image. Transport of c.e. joins constructs the
`DomainJoins` instance required by `RestrictionPredicates`; no independent
join assumption is added. The comparison is a bijective bounded lattice
homomorphism compatible with partial inverse image.

`NumericalEnumeration.lean` proves computability of counting and increasing
enumeration for recursive predicates. Infinitude of the carrier makes the
enumeration total; counting gives its inverse on the carrier.
`NumericalIsotype.lean` restricts these functions to the required source
objects and proves both partial-map inverse equations. This gives an
isomorphism with `ℕ` in both the numerical category and its total subcategory,
and hence the isotype property.

`NumericalTuring.lean` defines universal partial recursive evaluation using
the pinned program-code API. Partial application gives a computable total
parameter arrow for each numerical object. The factorization proof establishes
equality at every input, including outside the source carrier, and converts
totality to the restriction structure induced by the `P`-category.
`NumericalRecursion.lean` combines this result with isotype to construct
`PRecursionCategory Numerical`. Choice of a program code for each extensional
partial arrow defines `turingIndexing`, whose evaluation equation is proved.
This is a function between sets of arrows. Its internal realization is
constructed in `NumericalEnrichedTotals.lean`.

`TypeLattices.lean` internalizes bounded distributive lattices and their
homomorphisms in `Type`. The generalized-element operations are pointwise,
and monicity of the resulting internal map is equivalent to injectivity.
`NumericalEnriched.lean` internalizes the numerical hom-sets, category and
restriction operations, zeros, and partial products. Each equation is proved
for families at every parameter type.

`NumericalEnrichedDomains.lean` identifies the actual chosen equalizer of
restriction and identity with `Numerical.Domain`. It transports the domain
lattice to the equalizer and proves the generalized-family order isomorphism,
precomposition law, and partial inverse-image comparison. These give the
complete `EnrichedRestriction.DomainLattices` structure.

`NumericalEnrichedTotals.lean` identifies the actual chosen totality pullback
with the numerical total hom-set. Identities, composition, and pairing agree
under this equivalence. The indexing function lifts to an internal morphism;
its composite with the evaluation morphism is the identity. The evaluation
morphism is also expressed through internal composition and partial pairing
with the Turing evaluator. The numerical identity and zero remain distinct
as global enriched arrows.

`NumericalEnrichedPredicates.lean` gives the internal predicate action on all
PER subobjects, with identity, composition, and bounded lattice preservation
proved at every parameter type. The domain equalizer maps to its support
subobject. Injectivity proves monicity, and the partial inverse-image comparison
proves the naturality of this internal embedding.

`NumericalEnrichedGlobal.lean` evaluates global families at the unique element
of the terminal type. Constant families give inverse functors, producing
equivalences with the numerical partial and total categories. Restriction,
zeros, partial pairing, and projections agree under evaluation, and the
total-arrow equivalence preserves binary products.

`NumericalEnrichedSubobjects.lean` composes evaluation of global total arrows
with `toPER`. The composite preserves binary products. Evaluation of global
predicates gives an order isomorphism to the full PER subobject lattice;
its naturality is the categorical pullback equation. The resulting
`SubobjectIdentification` is the one required by the categorical theorem.
The generic enriched domain-to-subobject map agrees with the existing
numerical support-subobject map under these comparisons.

`PERFiniteLimits.lean` constructs a terminal PER and equalizers. The equalizer
restricts the source to inputs where the two representing functions return
related outputs. Its inclusion is monic, and each equalizing arrow factors
through it using the same representing partial recursive function. These
constructions give `HasFiniteLimits NumericalPER` without an enumerability
assumption on PERs or their supports.

`PERImages.lean` proves that including one PER relation in another with the
same support gives a regular epimorphism represented by the identity function.
Its coequalizer property is proved explicitly. For an arrow represented by
`f`, the image PER has the original source support and identifies two source
elements precisely when their outputs are related. This gives a regular
epimorphism followed by a monomorphism and hence a categorical image.
Every kernel pair has a coequalizer.

`PERPullbacks.lean` restricts the product to pairs whose images are related in
the common target. Recursive projections and pairing prove the pullback
universal property for arbitrary PER supports.

`PERRegular.lean` proves that a regular epimorphism has an invertible image
inclusion. A partial recursive function representing its inverse supplies
preimages of supported target representatives. Applying this function to the
image of the other cospan arrow and pairing with the original input gives a
section of the image inclusion of the pullback projection. That inclusion is
therefore an isomorphism, so the projection is a regular epimorphism.
Together with finite limits and kernel-pair coequalizers, this proves
`Regular NumericalPER`. Surjectivity on equivalence classes alone is not used
to infer the existence of a partial recursive selection of preimages.

`PERCoproducts.lean` constructs finite coproducts by coding the two summands
as pairs with first coordinate zero or one. The injections are monic, and the
empty PER is initial. `PERCoproductSquares.lean` proves the injection pullback
squares for a map of coproducts into the coproduct of two terminal objects.
The mediating functions recursively decode the second coordinate.

`PERCoproductDecomposition.lean` proves that the copairing of the two inverse
images of the summands is an isomorphism. For a function representing
`f : R → S + T`, the inverse evaluates `f` on an input `n`, uses the output's
first coordinate to choose the summand, and retains `n` and the output's
second coordinate as a pullback representative. Both inverse equations are
proved modulo the PER relations. The result is transported to chosen pullbacks
and arbitrary morphism classes.

`PERExtensive.lean` combines these two properties to prove the van Kampen
property for the coproduct of terminal objects. Mathlib's characterization
then gives `FinitaryExtensive NumericalPER`, and disjointness follows. Together
with regularity, this supplies the target-category assumptions in the numerical
interpretation without restricting PER supports to enumerable sets.

## Arithmetic syntax, representation, and incompleteness

`ArithmeticSyntax.lean` uses canonical syntax codes. The recursive increasing
enumeration and its rank give inverse computable maps between natural numbers
and arithmetic sentences. Unary-formula decoding assigns falsity to invalid
codes. `ArithmeticFormulaSubstitution.lean` compares Foundation's arithmetized
substitution with its syntax encoding and proves joint computability.
`ArithmeticNumericalSubstitution.lean` turns this into the total numerical
substitution arrow, returning a sentence-enumeration index.

`ArithmeticRepresentation.lean` defines strong numeralwise representation by
positive and negative proofs for each individual numeral. Consistency makes
the implications equivalences. The property persists under theory extension,
and Foundation's representation theorem supplies it for extensions of `PA⁻`.
`ArithmeticAdequacy.lean` identifies the categorical pullback equations with
these provability equivalences. Taking one parameter value gives a formula;
a fixed formula gives a constant recursive parameter arrow.

`ArithmeticRepresentationSection.lean` constructs the theory-specific internal
diagonal data and compares representation at every parameter type with the
numerical equations. Set-level choice of representing arrows supplies the
section of the representation pullback. Conversely, evaluation of a section
at constant global complementary pairs gives numeralwise definitions. No
uniform computable selection of formulas is required.

`ArithmeticEnumerableSupports.lean` proves that c.e. axioms give c.e. theorem
and refutation supports and constructs their numerical restriction domains.
`ArithmeticInseparability.lean` applies `enriched_no_global_separator` to the
section and numerical nontriviality, then uses the support comparison to
obtain recursive inseparability. `ArithmeticEssentialIncompleteness.lean`
proves that a complete consistent c.e. theory has recursive theorem support.
Such a support in an extension would separate the original theorem and
refutation supports. This proves the quantified essential-incompleteness
statement, as well as nonrecursiveness of theorem support in every consistent
extension.

## Remaining numerical constructions and verification

The next construction is the arithmetic Lindenbaum PER, its Boolean operations,
and the regular-epimorphism presentation by sentence indices. Its two bound
fibers must be identified with theorem and refutation predicates. Then the
theory-extension quotient maps and the Boolean-homomorphism correspondence in
`thm:integration-essential-equivalence` (iii) and
`prop:numerical-boolean-extensions` remain to be proved.

The effective-language generalization beyond arithmetic syntax and the c.e.
realization using only domain predicates `E` are not yet assembled. A single
record bundling the full definability-algebra data also remains absent.
The imported typed arithmetic program category remains a separate construction;
no equivalence with the numerical category is asserted.

The full verifier builds the combined entry point and audits 458 declarations,
after removal of the two disconnected arithmetic interface aliases. It checks
every pinned dependency and imported-source hash, as well as both manuscript
hashes. Thirteen imported files have comment-only revisions recorded in
`LOCAL_PATCHES.json`; their declarations and proofs are unchanged.
Palomar Comparator, NanoDa, and con-ron have not been run on this repository.
