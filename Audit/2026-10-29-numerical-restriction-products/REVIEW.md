# Numerical restriction products: source review

This review covers `NumericalPartialProducts`, `NumericalPCategory`,
`NumericalTotalProducts`, `NumericalTotalComparison`, and
`NumericalDomainComparison`. All five modules were read in full, together
with the imported restriction-product, total-arrow, and domain interfaces
used in their proofs. The manuscript comparison concerns the numerical
restriction products in `sec:integration-numerical` and the restriction,
product, and lattice data in `def:generalized-definability-algebra`.
The preceding checkpoint is `7befddd873d85750721aafb2f47f913cda082ddf`.

## A. Correctness findings

No concrete defect was found in the five modules. They construct partial
pairing and the P-category structure on the numerical category, identify
its induced restriction with the original numerical restriction, and
compare both its total products and domain lattice with the preceding
numerical constructions. Isotype, a Turing morphism, and the enriched
numerical structure remain to be constructed.

## B. Constructions and hypotheses

`NumericalPartialProducts` pairs two partial recursive functions using
recursive tuple coding. The pairing is defined exactly where both
components are defined. Each projection is restricted to the existing
recursive product carrier. The two projection equations include the
restriction of the other component, and the restriction of the pairing
is the intersection of the component domains. Precomposition distributes
over pairing because each partial function has at most one value at an
input. Pairing the projections of an arbitrary partial arrow recovers that
arrow, which also proves uniqueness from the two projections.

`NumericalPCategory` defines the product action, diagonal, and projections
using these operations. It proves bifunctoriality, the diagonal and
nested-projection identities, half-naturality of the projections, and
naturality of the associator and symmetry. Their membership formulas use
the corresponding recursive rearrangements of tuple codes. The class
instances are declared after these equations are proved. The two
zero-absorption laws separately establish the prodominical structure.

The equation `pcategory_rst_eq` identifies the restriction derived from
the product operations with partial identity on the original domain.
`inducedRestriction_eq` proves equality of the two restriction structures:
their operations agree on every arrow, and their remaining fields are
proofs of the restriction laws.

`NumericalTotalProducts` works in the original numerical total-arrow
category. Partial pairing of total arrows is total and satisfies both
ordinary product projection equations. Uniqueness for the existing product
cone identifies this arrow with its categorical lift. The explicit PER
product comparison then identifies its image under `toPER` with the PER
pairing.

`NumericalTotalComparison` constructs functors in both directions between
the total-arrow categories defined by the original and induced restrictions.
They retain each underlying object and arrow while converting the totality
proof with `pcategory_rst_eq`. The identity components give the unit and
counit of an equivalence, including their naturality and triangle equation.
The comparison identifies the two product pairings and preserves binary
products.

`NumericalDomainComparison` identifies the original numerical domains with
`DomSemilattice` domains by an order isomorphism retaining their underlying
endomorphisms. The order on both sides is restriction composition. The
comparison identifies composition as meet and commutes with restriction
inverse image along every partial arrow. Transporting c.e. unions supplies
the joins, their least-upper-bound laws, distributivity, and inverse-image
stability required by `DomainJoins`. The resulting bounded lattice
homomorphism is bijective and retains the inverse-image equation.

## C. Local issues

The full verifier passed after all five modules were complete: the build
finished with 1,941 jobs, and all 311 axiom audits passed, retaining the
preceding 273 declarations. The five new modules produced no warnings;
the two pre-existing imported linter warnings remain. The verification
logs, source hashes, and scan of the 56 project Lean files are recorded
separately in this directory.

The comments state the operations and equations directly. They distinguish
partial pairing from the categorical pairing of total arrows. No
terminology or prose defect requiring a source change was found. This
review does not make a whole-manuscript editorial judgment.

## D. Consistency and dependency check

The numerical category continues to use infinite recursive subsets of
the natural numbers as objects. The previously constructed product carrier
is recursive and infinite. A terminal object or singleton numerical object
is not required by the P-category interface.

The imported `TotalSubcategory` definition records the restriction induced
by the P-category, whereas the original `Numerical.Total` records the
original restriction. The new functors compare these definitions explicitly.
The priority adjustment for `numericalRestriction` is local to the
P-category module; it is not used as a replacement for the restriction
comparison theorem.

The product laws apply to partial arrows. Full naturality of either
projection is not asserted; the corresponding projection equation retains
the restriction of the other component. Associator and symmetry naturality
are proved for arbitrary partial component arrows.

The domain lattice remains the lattice of c.e. supports. Its joins are
constructed, and no complementation assumption is introduced. The
`DomainJoins` interface requests join preservation along total arrows; the
numerical proof uses the already established preservation along all partial
arrows. The PER predicate lattice and its natural domain embedding are
unchanged.

No new unproved axiom or assumption restating a desired conclusion occurs
in these modules. Domain splitting, ranges, isotype, and recursion are not
assumed to obtain the product or domain results. No imported source or
manuscript file was changed in this checkpoint.

## E. Remaining requirements

The next construction is a recursive isomorphism between every infinite
recursive numerical carrier and the natural numbers. These isomorphisms
will establish the isotype property. A universal evaluator and its
parameterization equations are then needed for the numerical Turing
morphism and recursion-category instance.

The Set-enriched structure and its comparison with the ordinary numerical
category still require explicit construction. Effective syntax, numeral
substitution, the Lindenbaum Boolean presentation, and theory-extension
quotients remain necessary for the arithmetic interpretation. Numeralwise
provability of individual instances must remain distinct from provability
of a single universally quantified sentence.

## F. Scope and assessment

The numerical restriction products, prodominical structure, total-product
comparisons, and domain-lattice comparison are established. The numerical
recursion category and its arithmetic interpretation remain incomplete.
No additional suspected mathematical defect was identified in the reviewed
modules. This review did not check other manuscript claims or new literature
references. Palomar Comparator, NanoDa, and con-ron were not run.
