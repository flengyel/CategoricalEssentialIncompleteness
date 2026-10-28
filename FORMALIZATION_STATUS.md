# Formalization status: version 16

The external diagonal theorem, its global inseparability consequence, the
Boolean-presentation lemma, and the equivalence between complete represented
extensions and represented decisions are proved. The full enriched categorical
theorem and its numerical interpretation are not yet formalized. All declarations below are in the namespace
`CategoricalEssentialIncompleteness`.

## Correspondence

| Manuscript label | Lean declaration or module | Status |
| --- | --- | --- |
| `eq:integration-rows` | `DiagonalData.Represents` | Both representation equations, with the same total arrow and separate objects `U`, `S`. |
| `thm:integration-diagonal` | `DiagonalData.integration_diagonal`; `restriction_integration_diagonal` | Proved. The latter uses actual `DomSemilattice` elements and `RestrictionCategory.TotalSubcategory`. |
| `cor:definability-algebra-inseparability` | `DiagonalData.inseparable`; `restriction_inseparable` | Proved from representation of every complementary pair. Extraction of that representation from an enriched section remains to be implemented. |
| `thm:internal-inseparability` | `parameterized_separator_factorization` | Conditional bridge proved over an arbitrary finitely complete base. Construction of its parameterized input from the enriched algebra, at the actual object `Sep`, remains open. |
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

## The enriched bridge still required

`parameterized_separator_factorization` proves an actual arrow into the
equalizer of the two global bounds, with its factorization equation. Its
inputs include a separator and representative in a category of parameterized
arrows, and an interpretation of that domain lattice as arrows from the
parameter object into `E_U`, preserving the two bounds. It assumes neither
the equality of those bounds nor the requested factorization.

To recover `thm:internal-inseparability`, construct these inputs for the
parameter object `Sep` from the enriched hom-objects, the internal lattice
objects, their equalizers and pullbacks, and the section `sigma`. In
particular, `g = rho gamma` must be an arrow with parameter `Sep`.
Representation merely at global points does not fill this obligation.
The strict-initial-object consequence is also not yet implemented.

The next unresolved categorical construction is the generalized representative
at the actual object `Sep`, obtained from the enriched section and the
internal complementary-pair object. This must supply the input to
`parameterized_separator_factorization` and connect the global representation
data to the manuscript's functor `J`. The completed Boolean decision
equivalence does not replace that construction.

## Numerical and verification boundaries

No equivalence between the imported typed arithmetic program category and the
manuscript's numerical category or PER presentation is asserted. That bridge
must compare objects, arrows and their equality, restriction domains, numeral
substitution, and the theorem/refutation fibers. Numeralwise provability has
the form “for every numeral, there exists a proof of the corresponding
instance”; it must not be replaced by provability of one universally
quantified sentence.

The full verifier builds the combined entry point and audits 47 declarations,
retaining all eleven original audits. It also checks every pinned dependency
and imported source hash. No imported source was changed for this milestone.
Lean compilation and axiom inspection do not establish the open comparisons
above or completion of the imported Rice–Shapiro program. Palomar Comparator,
NanoDa, and con-ron have not been run on this repository.
