# Numerical Set-enrichment: source review

This review covers `TypeLattices`, `NumericalEnriched`,
`NumericalEnrichedDomains`, `NumericalEnrichedTotals`,
`NumericalEnrichedPredicates`, `NumericalEnrichedGlobal`, and
`NumericalEnrichedSubobjects`. All seven modules were read in full, together
with the internal hom, restriction, lattice, predicate, global-comparison,
and Type-limit interfaces used in their proofs. The manuscript comparison
concerns `def:generalized-definability-algebra`, the indexing structure
preceding that definition, and `sec:integration-numerical`.
The preceding checkpoint is `fcea3cce61067fdad81796f0d4a31cd46b09054e`.

## A. Correctness findings

No concrete defect was found in the seven modules. They construct the
numerical hom-objects in `Type`, enriched restriction products and zeros,
internal domain lattices, total hom-objects, internal indexing, and full
PER subobject predicates with a monic natural domain embedding. The global
partial and total categories are compared with the numerical categories
by explicit equivalences. The global predicates are naturally identified
with subobjects along the resulting product-preserving PER functor.
The theory-dependent substitution, predicates, representation section,
and Boolean presentation remain to be constructed.

## B. Constructions and hypotheses

`TypeLattices` transports the pointwise bounded distributive lattice on
functions to categorical morphisms of types. Precomposition preserves
the lattice operations and bounds at every parameter type. A bounded
lattice homomorphism gives an internal homomorphism by postcomposition,
with the corresponding preservation equations. Its monicity is equivalent
to injectivity by the categorical characterization of monomorphisms in
`Type`. The generic hom-lattice definitions are installed as local
instances in the modules that use them.

`NumericalEnriched` takes the existing numerical hom-sets as hom-objects.
Composition and partial pairing use the projections of the chosen Type
products. Their evaluation lemmas prove agreement with the numerical
operations at every parameter. The restriction equations are proved
pointwise using the original numerical restriction structure explicitly.
The restriction-product laws retain the restriction of the other
component in each pairing/projection equation. The projections are total,
and partial pairing satisfies its reconstruction equation. The
nowhere-defined numerical arrows supply enriched zeros and their
composition and restriction equations.

`NumericalEnrichedDomains` compares the actual chosen equalizer of
restriction and identity with `Numerical.Domain` through
`Types.equalizerIso`. It transports the existing numerical bounded
distributive lattice to that equalizer. The family equivalence and order
isomorphism apply to every parameter type, and reindexing these families
is ordinary precomposition. Restriction inverse image agrees pointwise
with numerical domain inverse image. The resulting `DomainLattices`
instance identifies meet with composition, top with identity, and bottom
with zero. Preservation of joins follows from the existing numerical
inverse-image theorem for arbitrary partial arrows.

`NumericalEnrichedTotals` compares the actual totality pullback with
the hom-set of `Numerical.Total`. Its forward map evaluates the pullback
inclusion, and its inverse is obtained from the pullback universal
property applied to the family of all total arrows. The inclusion
equation and its monicity prove the two inverse identities. Internal
identities, composition, and pairing agree with their numerical total
counterparts at every parameter. Evaluating global identity and zero at
the terminal point also proves their inequality at the numerical object
of all natural numbers.

The same module lifts the existing numerical indexing function to an
arrow into the internal total hom-object. Its evaluation arrow forms the
product of a total parameter arrow with the identity and then composes
with the Turing morphism. `internalEvaluation_composition` identifies this
description with the internal composition and pairing operations for
every family. `internalIndexing_evaluation` proves the section equation
as an equality of Type morphisms. At `V = nat`, these are the indexing
and evaluation arrows required by the manuscript.

`NumericalEnrichedPredicates` uses all categorical PER subobjects as its
predicate objects. Pullback is defined pointwise along the total-arrow
equivalence, with identity and contravariant composition equations.
The internal domain map is the composite of the equalizer order
isomorphism and the existing numerical bounded lattice homomorphism to
support subobjects. Its injectivity proves monicity. Naturality for
every parameter type follows from the numerical subobject pullback
comparison and the internal domain inverse-image comparison.

`NumericalEnrichedGlobal` constructs evaluation at the unique terminal
point and the inverse constant-family functor. The inverse identities,
naturality of the identity components, and triangle equations give an
equivalence of the partial-arrow categories. Evaluation preserves
restriction, zeros, and partial pairing and projections. The explicit
totality comparisons give an equivalence of the total-arrow categories;
this equivalence preserves binary products.

`NumericalEnrichedSubobjects` composes total evaluation with `toPER`,
obtaining the required binary-product-preserving functor from global
total arrows to PERs. Evaluation of a global predicate is an order
isomorphism with the full subobject lattice. Its inverse is the constant
family, and order reflection uses uniqueness of the terminal point.
The comparison between a lifted global total arrow and its numerical
evaluation proves naturality for categorical pullback. Finally,
`enriched_domainSubobject_apply` identifies the generic domain-to-subobject
construction with the existing numerical support-subobject map.

## C. Local issues

The recorded full verification passed: the build completed with 1,956 jobs,
and all 383 axiom audits passed, retaining the preceding 336 declarations.
The audited dependencies are confined to `propext`, `Classical.choice`,
and `Quot.sound`. The verification record contains 68 integration hashes,
including the verifier. The source scan covers 67 project Lean files and
reports no matches for proof omissions or unproved declaration forms.
The two pre-existing imported linter warnings remain. These conclusions
were checked against the recorded logs and JSON reports; this source
review did not itself run Lean or the verifier.

The source introduces each construction before its comparison equations.
The comments distinguish partial pairing, total products, domain
equalizers, and general subobject predicates. The supplied copy of Knuth,
Larrabee, and Roberts's *Mathematical Writing*, Section 1, was consulted
for the prose review. No terminology defect requiring a source change
was found. This review makes no whole-manuscript editorial judgment.

## D. Consistency and dependency check

The internal structures use the chosen finite limits in `Type`. The domain
and total comparisons are proved through the equalizer and pullback
universal properties. The pointwise equations hold for arbitrary
parameter types; global evaluation is used separately when comparing
the ordinary categories and predicates.

The numerical restriction used by the enriched structure is the original
partial identity on the domain. The internal totality pullback is compared
with `Numerical.Total`, which uses the same restriction. The preceding
checkpoint's equality with the P-category-induced restriction remains
available, and no new instance-priority adjustment is introduced here.

The domain lattice remains the lattice of c.e. supports. The predicate
lattices contain all PER subobjects, and the internal domain maps preserve
bounds, meets, and joins without assuming that every domain is
complemented. No distinguished theorem or refutation predicate is assumed
to lie in the domain embedding's image.

The internal indexing arrow is a morphism in the category of types.
Its construction uses the previously justified choice of a program code
for each extensional partial recursive arrow. It imposes no additional
computability requirement on the set of arrows. The evaluation section
proved here is distinct from the representation section whose equations
involve the two distinguished predicates.

No new unproved axiom or hypothesis restating a desired conclusion occurs
in the seven modules. No imported source, dependency pin, or manuscript
file changed in this checkpoint. The comparison with the numerical
category does not identify it with the imported typed arithmetic program
category. A single record for the entire definability algebra and a
comparison with Mathlib's bundled enriched-category interface are not
provided by these modules.

## E. Remaining requirements

The next construction is effective sentence and unary-formula coding,
including a recursive substitution function that varies both the formula
code and the numeral. Its interpretation must give the numerical total
arrow `s` used in the manuscript. The sentence-code bijection, treatment
of invalid formula codes, and identification of its output sentence
must be proved for the selected syntax.

The remaining dependencies are:

1. Construct the theorem and refutation support predicates for a theory
   and prove their disjointness from consistency.
2. Prove `prop:integration-arbitrary-adequacy`, relating the two
   representation equations to strong numeralwise definability. Then
   construct the actual section on complementary domain pairs in
   `cor:numerical-definability-algebras`.
3. Construct the Lindenbaum PER Boolean algebra and its presentation by
   a regular epimorphism, and identify its two bound fibers.
4. Prove the theory-extension quotient correspondence, the characterization
   of represented fibers by c.e. axiomatizability, and the comparison of
   categorical and logical completeness. The interpretation of Boolean
   maps also requires the complete decidable extension correspondence
   and effective completion of decidable theories.
5. Apply numeralwise representability in PA and its preservation under
   theory extension to obtain the arithmetic corollary.

The pinned Foundation file
`Foundation/FirstOrder/Arithmetic/R0/Representation.lean` supplies
`codeOfComputablePred_provable` and
`codeOfComputablePred_provable_neg`. They give positive numeral-instance
proofs under extension of `R₀` and negative numeral-instance proofs under
extension of `PA⁻`, respectively, without a soundness hypothesis.
They can supply the arithmetic representation implications after the
formula-coding and substitution comparisons are proved.
`Arith.FixedFormulaNumeralSubstitution` treats fixed formulas; it does
not alone establish the required joint substitution function.
Numeralwise provability of individual instances must remain distinct
from provability of one universally quantified sentence.

## F. Scope and assessment

The numerical restriction, lattice, predicate, indexing, global-category,
and subobject-identification constructions reviewed here are established.
The general categorical essential-incompleteness theorem was proved in
an earlier checkpoint. Its concrete arithmetic application still requires
the syntax, representation section, and Lindenbaum comparisons above.
Part (ii) of `thm:integration-essential-equivalence` is already proved
for arbitrary disjoint supports. Parts (i) and (iii),
`prop:numerical-boolean-extensions`, and the arithmetic corollary remain
open.

No confirmed or suspected mathematical defect was identified in the seven
reviewed modules. The unresolved arithmetic comparisons are the principal
remaining requirement for the intended application. This review did not
assess other manuscript claims, novelty, or new literature references.
Palomar Comparator, NanoDa, and con-ron were not run.
