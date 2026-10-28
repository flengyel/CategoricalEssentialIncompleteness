# Formalization status: version 16

The external diagonal theorem, its global inseparability consequence, and the
Boolean-presentation lemma are proved. The full enriched categorical theorem
and its numerical interpretation are not yet formalized. All declarations below are in the namespace
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
| `prop:complete-extensions-and-decisions` | — | Open. |
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

The next Boolean construction is `prop:complete-extensions-and-decisions`:
construct the internal Boolean algebra on the coproduct of two terminal
objects, prove that its bound copairing into every internal Boolean algebra is
a Boolean homomorphism, and relate characteristic arrows to complementary
subobjects in the image of `j_S`. The enriched input construction remains a
separate prerequisite for the full central theorem.

## Numerical and verification boundaries

No equivalence between the imported typed arithmetic program category and the
manuscript's numerical category or PER presentation is asserted. That bridge
must compare objects, arrows and their equality, restriction domains, numeral
substitution, and the theorem/refutation fibers. Numeralwise provability has
the form “for every numeral, there exists a proof of the corresponding
instance”; it must not be replaced by provability of one universally
quantified sentence.

The full verifier builds the combined entry point and audits 33 declarations,
retaining all eleven original audits. It also checks every pinned dependency
and imported source hash. No imported source was changed for this milestone.
Lean compilation and axiom inspection do not establish the open comparisons
above or completion of the imported Rice–Shapiro program. Palomar Comparator,
NanoDa, and con-ron have not been run on this repository.
