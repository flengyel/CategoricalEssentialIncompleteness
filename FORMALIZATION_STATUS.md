# Formalization status: version 16

The external diagonal theorem, its global inseparability consequence, the
Boolean-presentation lemma, and the equivalence between complete represented
extensions and represented decisions are proved. The internal factorization
`Sep → Z_U` is also proved for explicit internal total-arrow and predicate
structures, using the actual representation section and separator equalizer.
The full enriched categorical theorem and its numerical interpretation are not
yet formalized. All declarations below are in the namespace
`CategoricalEssentialIncompleteness`.

## Correspondence

| Manuscript label | Lean declaration or module | Status |
| --- | --- | --- |
| `eq:integration-rows` | `DiagonalData.Represents` | Both representation equations, with the same total arrow and separate objects `U`, `S`. |
| `thm:integration-diagonal` | `DiagonalData.integration_diagonal`; `restriction_integration_diagonal` | Proved. The latter uses actual `DomSemilattice` elements and `RestrictionCategory.TotalSubcategory`. |
| `cor:definability-algebra-inseparability` | `DiagonalData.inseparable`; `restriction_inseparable` | Proved from representation of every complementary pair. The internal section now supplies representatives at every parameter; its comparison with the restriction-category presentation remains open. |
| `eq:v8-complement-pullback` | `InternalLattice.Complements`; `InternalLattice.liftComplement` | Actual pullback, universal complementary pair, and lift at every parameter constructed. |
| `eq:v8-representation-pullback`; `eq:v8-representation-section` | `InternalDiagonalData.Representation`; `representation_section_iff`; `RepresentationSection.represents` | Actual pullback and section; equivalence with the universal representation equations; generalized representatives derived. The latter two names are in `InternalDiagonalData`. |
| `thm:internal-inseparability` | `InternalDiagonalData.internal_inseparability`; `no_global_separator`; `separatorIsInitial` | Factorization at the actual `Sep` and both consequences proved for explicit internal total-arrow/predicate data over an arbitrary finitely complete base. Construction of that data from enriched restriction hom-objects remains open. The latter two names are in `InternalDiagonalData`. |
| `lem:complete-boolean-presentation` | `BooleanPresentation.consistent_iff_mono`; `BooleanPresentation.complete_iff_regularEpi`; `BooleanPresentation.consistent_complete_iff_isIso` | Proved in a regular extensive category, with actual equalizer fibers and the actual bound copairing. |
| `thm:categorical-essential-incompleteness` | `boolean_quotient_incomplete`; `boolean_quotient_boundCopair_not_regularEpi` | The external quotient argument and its equivalent conclusion about the bound copairing are proved for genuine Boolean presentations, regular epimorphisms, and subobject fibers. The full enriched input construction remains open. |
| `prop:complete-extensions-and-decisions` | `complete_extensions_and_decisions`; `PredicateEmbedding.complete_extensions_and_decisions` | Proved for genuine Boolean quotients and the constructed internal Boolean algebra on `1 + 1`. The second declaration uses the existing `E`-to-`P` embedding followed by the subobject identification. |
| Boolean-homomorphism conclusion of `cor:integration-no-boolean-map` | `no_represented_boolean_decision` | Proved from the external diagonal representation data. This does not claim the arbitrary-arrow clause or the full enriched input construction. |
| `thm:integration-essential-equivalence` | — | Open; needs the numerical recursion category, PER category, and syntax/provability comparison. |
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
binary restriction products. It packages the existing domain order and
composition as a distributive lattice with the following explicit additional
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
hom-sets. `BooleanPresentation` and `BooleanQuotient` include actual
`IsRegularEpi` proofs, and the induced presentation is constructed.

`boundFiber` is the actual equalizer subobject of the presentation and the
constant bound arrow. `boundFiber_le_postcomp` proves the two inclusions used
in the quotient argument. `boolean_quotient_incomplete` assumes a regular
extensive category, an order isomorphism from `P(S)` to its relevant subobject
lattice, and the external representation data. It proves that consistent
represented quotient fibers cannot have join top. Since the external data
are already supplied, this proof only needs the identification at `S`; it
does not yet construct that data from the manuscript's functor `J` and its
natural identification at every object.

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

`TwoBoolean.lean` constructs Boolean operations as actual arrows on `1 + 1`.
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
`1 + 1` is a split epimorphism, so it gives a genuine Boolean quotient. The
characteristic-arrow fiber equations identify its two represented fibers.
`PredicateEmbedding.subobjectMap` and the specialized equivalence keep the
restriction-domain sort `E(S)` distinct from the general-predicate sort `P(S)`.
The final `no_represented_boolean_decision` result combines this equivalence
with the existing external diagonal obstruction.

## The internal separator construction and remaining enriched bridge

`InternalLattices.lean` describes a bounded distributive lattice object by its
lattice structures on all generalized-element hom-sets, natural under
precomposition. It constructs the representing meet and join arrows and the
actual complementary-pair pullback. Its two projections are complementary,
and a complementary pair at every parameter has a lift to this pullback.

`InternalCartesian.lean` specifies hom-objects, composition, identity, and
binary-product operations as morphisms in the base. `CartesianLaws` gives the
category and binary-product equations at all parameters. `InternalPredicates`
specifies internal action arrows, bounded lattice preservation, and the
identity and contravariant composition equations. `InternalPredicateEmbedding`
has actual monic components; injectivity at arbitrary parameters is derived
from monicity. None of these fields assumes separator collapse or a
factorization through the bound equalizer.

`InternalDiagonalData.diagonal_collapse` proves the diagonal calculation at
any parameter object. `InternalRepresentation.lean` forms the actual pullback
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

The next unresolved lemma is the construction of this **internal total-arrow
reduct from enriched restriction hom-objects**: define `E_X` as the fixed-point
equalizer of restriction and `T(X,Y)` as its totality pullback; construct
composition and chosen binary products on `T`; derive their equations and the
restriction inverse-image action. The lattice sort `E` in the new internal
modules is not yet identified with that equalizer. The existing external
`RestrictionPredicates.lean` construction does not itself establish this
internal comparison. The global-element comparison must then connect the
internal section to the existing external `DiagonalData` and to the functor
`J` and its natural subobject identification. Until these bridges are proved,
the full enriched categorical theorem is not claimed.

## Numerical and verification boundaries

No equivalence between the imported typed arithmetic program category and the
manuscript's numerical category or PER presentation is asserted. That bridge
must compare objects, arrows and their equality, restriction domains, numeral
substitution, and the theorem/refutation fibers. Numeralwise provability has
the form “for every numeral, there exists a proof of the corresponding
instance”; it must not be replaced by provability of one universally
quantified sentence.

The full verifier builds the combined entry point and audits 62 declarations,
retaining all eleven original audits. It also checks every pinned dependency
and imported source hash. No imported source was changed for this milestone.
Lean compilation and axiom inspection do not establish the open comparisons
above or completion of the imported Rice–Shapiro program. Palomar Comparator,
NanoDa, and con-ron have not been run on this repository.
