# Formalization status: version 16

The external diagonal theorem, its global inseparability consequence, the
Boolean-presentation lemma, and the equivalence between complete represented
extensions and represented decisions are proved. The internal factorization
`Sep → Z_U` is also proved from enriched restriction and predicate data. The
domain equalizers, totality pullbacks, internal total-arrow operations, and
restriction inverse-image action are constructed, and the proof uses the
representation section and separator equalizer.
The global total-arrow, domain, representation, and predicate comparisons are
proved. The categorical theorem is stated along `J : Tot(K₀) → C`, with
restriction idempotents and a natural subobject identification. It uses
the restriction, lattice, predicate, and section data of a definability algebra;
the additional recursion and indexing data are unused. The numerical
restriction category, PER category, full faithful functor, domain/support
comparison, support subobjects, pullbacks, and c.e. joins are constructed.
The numerical separator equivalence, binary products and their preservation
by `J`, PER finite limits, regular-image factorizations, and coequalizers of
kernel pairs are proved. Pullback stability, coproducts, extensivity, and
the arithmetic interpretation remain open. All declarations below are in the namespace
`CategoricalEssentialIncompleteness`.

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
| `thm:categorical-essential-incompleteness` | `EnrichedRestriction.categorical_essential_incompleteness`; `categorical_boundCopair_not_regularEpi` | Both conclusions proved along `J : Tot(K₀) → C`, from the internal section, natural predicate identification, and ordinary representing restriction idempotents. Both names are in `EnrichedRestriction`; the precise input scope is described below. |
| `prop:complete-extensions-and-decisions` | `complete_extensions_and_decisions`; `EnrichedRestriction.global_complete_extensions_and_decisions` | Proved for Boolean quotients and the constructed internal Boolean algebra on `1 + 1`, including the specialization to ordinary restriction domains and the identification along `J`. |
| Boolean-homomorphism conclusion of `cor:integration-no-boolean-map` | `no_represented_boolean_decision`; `EnrichedRestriction.global_no_boolean_decision` | Proved, including the specialization along `J` from the internal section. The arbitrary-arrow clause is not claimed. |
| Numerical category and domain identification in `sec:integration-numerical` | `Numerical.numericalRestriction`; `Numerical.domainSupportOrderIso`; `Numerical.recursive_iff_complemented_support` | Extensional partial recursive arrows, restriction laws, c.e. domain lattice, partial inverse image, and recursive/complemented equivalence proved. Binary products of total arrows are constructed; restriction products and the recursion-category instance remain open. |
| PER category and functor `J` in `sec:integration-numerical` | `NumericalPER.perCategory`; `Numerical.toPER`; `Numerical.toPER_full`; `Numerical.toPER_faithful` | Arbitrary PERs and arrows defined by equivalence classes of representing functions constructed. The functor is full and faithful and preserves binary products. Finite limits and regular-image factorizations are constructed; pullback stability and extensivity remain open. |
| Binary products and preservation by `J` in `sec:integration-numerical` | `Numerical.productIsLimit`; `Numerical.toPER_preservesBinaryProducts` | Recursive tuple coding gives infinite recursive product carriers. Projection equations for the PER comparison prove preservation. |
| Finite limits and regular images in `sec:integration-numerical` | `NumericalPER.perHasFiniteLimits`; `imageFactorisation`; `hasCoequalizer_of_isKernelPair` | Terminal object, products, equalizers, and regular-epimorphism/monomorphism factorizations are constructed. Every kernel pair has a coequalizer. The latter two declarations are in `NumericalPER`. |
| Support order and inverse image in `lem:integration-numerical-subobjects` | `NumericalPER.supportSubobject_le_iff`; `supportSubobject_eq_iff`; `inverse_isPullback` | Subobjects and the full pullback universal property proved for arbitrary supports. All names are in `NumericalPER`. |
| C.e. joins and the image of `j` in `lem:integration-numerical-subobjects` | `NumericalPER.enumerable_union_isLUB`; `Numerical.domainSubobject`; `Numerical.supportSubobject_in_range_iff` | The union is least among all categorical upper bounds. The domain map is an order embedding whose image among support inclusions is exactly c.e. supports. Its full bounded lattice homomorphism structure and the Boolean-fiber assertions remain open. |
| `thm:integration-essential-equivalence` (ii) | `Numerical.no_separator_iff_recursively_inseparable` | The support statement is proved for arbitrary disjoint supports, with PER subobject inequalities and numerical restriction domains. |
| `thm:integration-essential-equivalence` (i), (iii), and its theory instance | — | Open; needs the remaining numerical/PER structure and the syntax/provability comparison. |
| `prop:numerical-boolean-extensions` | — | Open. |
| `cor:arithmetic-representation-incompleteness` | — | Open; the imported arithmetic recursion-category instance is not this numerical comparison. |

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
along `J`, and `CategoricalTheorem.lean` states the conclusion using ordinary
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

`CategoricalTheorem.lean` states the principal theorem with ordinary
nontriviality `1_U ≠ 0`, a regular extensive target, a binary-product-preserving
functor `J`, the natural identification, Boolean presentations and
quotients, and representing ordinary restriction idempotents. It proves
incompleteness and the bound-copairing conclusion. It also specializes the
decision equivalence and excludes represented Boolean decisions.

The precise input scope is the restriction, product, zero, lattice, predicate,
and representation-section part of Definition `def:generalized-definability-algebra`.
The proof does not use the additional recursion-category or indexing data.
Product preservation by `J` is retained in the principal statement, although
the quotient argument needs only the identification component at `S`.
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
universal property. This does not yet construct the `PCategory` restriction
products or the numerical recursion-category instance.

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
Every kernel pair has a coequalizer. Pullback stability of regular epimorphisms
is the remaining regularity obligation; no `Regular NumericalPER` instance is
assumed or declared.

## Numerical and verification boundaries

No equivalence between the imported typed arithmetic program category and the
manuscript's numerical category or PER presentation is asserted. That comparison
must identify objects, arrows and their equality, restriction domains, numeral
substitution, and the theorem/refutation fibers. Numeralwise provability has
the form “for every numeral, there exists a proof of the corresponding
instance”; it must not be replaced by provability of one universally
quantified sentence.

The next unresolved lemma is **pullback stability of regular epimorphisms
in the PER category**. Coproducts and extensivity must then be constructed,
and the numerical domain map made into the required natural bounded lattice
homomorphism. The Turing/indexing and Set-enrichment data, effective syntax, numeral
substitution, Lindenbaum Boolean presentation, and theory-extension quotients
also remain open. They are needed for `thm:integration-essential-equivalence`
(i) and (iii), `prop:numerical-boolean-extensions`, and the arithmetic corollary.

The full verifier builds the combined entry point and audits 179 declarations,
retaining all eleven original audits. It also checks every pinned dependency
and imported source hash, as well as both manuscript hashes. Twelve imported
files have comment-only revisions recorded in `LOCAL_PATCHES.json`; their Lean
declarations and proofs are unchanged. Original source pins are retained.
Lean compilation and axiom inspection do not establish the open comparisons
above or completion of the imported Rice–Shapiro program. Palomar Comparator,
NanoDa, and con-ron have not been run on this repository.
