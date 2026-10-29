# Numerical domains and subobject predicates: source review

This review covers `NumericalSupportLattice`, `NumericalDomainReindexing`,
`NumericalDomainEmbedding`, `SubobjectPredicates`, and `NumericalPredicates`.
All five modules were read in full, together with the image, coproduct, and
pullback results used in their proofs. The manuscript comparison concerns
Lemma `lem:integration-numerical-subobjects` in version 16. Compilation and
axiom inspection are recorded separately in this directory.

## A. Correctness blockers

No concrete defect was found in the five modules. They construct the numerical
restriction-domain lattices, the full PER subobject lattices, and the injective
natural bounded lattice homomorphism between them. The characterization of
Boolean arrows, their fibers, and complemented subobjects remains unproved
for the numerical presentation.

## B. Constructions and hypotheses

`NumericalSupportLattice` identifies the full-support inclusion with the top
subobject and the empty-support inclusion with the bottom subobject. The
intersection inclusion represents the categorical meet for arbitrary supports.
For two computably enumerable supports, their union inclusion represents the
categorical join. The join theorem retains both enumerability hypotheses and
uses a least-upper-bound result in the full subobject order.

`NumericalDomainReindexing` proves preservation of bottom, binary meets, and
binary joins by inverse image along partial numerical arrows. Preservation
of top requires a total arrow. Identity and composition laws then define
bounded lattice homomorphisms on restriction domains along total arrows.
Composition is contravariant: inverse image along `f ≫ g` is inverse image
along `g` followed by inverse image along `f`.

`NumericalDomainEmbedding` identifies inverse image of a domain with the
categorical pullback of its support inclusion. The support calculations prove
preservation of bounds, meets, and joins by `domainSubobjectHom`; the join
proof uses the enumerability of restriction domains. The homomorphism is
injective. Its complementarity theorem preserves and reflects complementarity
of a specified pair of domains.

`SubobjectPredicates` works in an arbitrary regular finitely extensive
category. Stability of regular epimorphisms under pullback proves that images
commute with pullback. Extensivity and the expression of a join as the image
of a coproduct arrow then prove preservation of binary joins by pullback.
The map-pullback adjunction for a monomorphism gives preservation of joins by
its direct-image map. These results prove distributivity of the subobject
lattice. Together with preservation of meets and bounds, they define the
contravariant predicate lattice `subobjectPredicates`.

`NumericalPredicates` applies this construction to the previously established
regular and finitely extensive PER category. On the category of total
numerical arrows, `domainPredicates` supplies the restriction-domain family
`E`, and `predicates` supplies the family
`P(X) = Subobject (toPER.obj X)`. The definition `domainEmbedding` supplies
the injective natural bounded lattice homomorphism `j : E → P`.
The identification `predicateSubobjectIdentification` is the identity order
isomorphism at each object and satisfies the required naturality equation.

## C. Local issues

The full verifier passed: the project build completed with 1,931 jobs, all
247 axiom audits passed, and the source-hole scan found no prohibited
declarations in the 46 project Lean files. All 213 previously audited
declarations are retained. The five new modules produced no warnings.
The verified source hashes match the final source. No imported Lean source
was changed.

The mathematical comments state the constructions and their hypotheses
directly. No concrete terminology or prose defect requiring a change was
found in these modules. This assessment does not constitute a review of the
entire manuscript.

## D. Consistency and dependency check

The predicate family uses all categorical subobjects of the relevant PER
objects. Support inclusions form a specified family within these lattices;
the construction does not identify the full subobject lattice with a powerset.
The join comparison for support inclusions requires computable enumerability,
whereas the generic preservation of categorical joins by pullback requires
regularity and finite extensivity. These are separate statements with separate
hypotheses.

Restriction idempotents and general predicates remain distinct. Injectivity
of `j` does not assert surjectivity. The complementarity result applies to two
given domains and does not assert that every restriction idempotent is
complemented. No complementability, decidability, or enumerability condition
is added to arbitrary PER subobjects. No new unproved axiom or premise
restating a desired conclusion occurs in these constructions.

## E. Remaining requirements

The next construction is the remaining part of
`lem:integration-numerical-subobjects`: identify arrows from the equality PER
on the natural numbers to the Boolean object with total recursive Boolean
functions; identify their fibers over `1` with the images under `j` of
recursive subsets; and
prove that these fibers are precisely the complemented subobjects. The last
step must apply to arbitrary complemented PER subobjects, using their
coproduct decomposition.

Numerical restriction products and recursion/indexing data, the enriched
structure, and their compatibility with the functor to PERs remain to be
established. The syntactic Boolean presentation, theory-extension quotients,
and arithmetic representation comparison remain open. Numeralwise provability
of individual instances must remain distinct from provability of a single
universally quantified sentence.

## F. Scope and assessment

This checkpoint proves the natural bounded lattice embedding required by the
first part of the numerical subobject lemma. The strongest confirmed
limitation is the incomplete numerical instantiation of the categorical
theorem and its arithmetic interpretation. No additional concrete suspected
defect was found in the reviewed modules. Lean compilation and axiom
inspection do not establish the remaining manuscript results. Palomar
Comparator, NanoDa, and con-ron were not run.
