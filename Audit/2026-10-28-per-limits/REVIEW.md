# Proof scope: products, finite limits, and regular images

This is an author-side source review of `PERProducts`, `NumericalProducts`,
`PERFiniteLimits`, and `PERImages`. Compilation and transitive axiom inspection
are recorded separately. The review does not certify the full manuscript.

## A. Correctness blockers

No concrete error was found in the four constructions. The full numerical
application remains incomplete: pullback stability of regular epimorphisms,
extensivity, the numerical recursion-category structure, and the arithmetic
syntax and provability comparisons are not supplied by this checkpoint.

## B. Principal constructions and their hypotheses

`PERProducts` uses recursive pairing of natural numbers to construct products
of arbitrary PERs. Projection and pairing equations hold on supported inputs
modulo the target PER relation; morphisms remain equivalence classes of
representing partial recursive functions.

`NumericalProducts` constructs infinite recursive product carriers and binary
products in the category of total numerical arrows. The comparison with PER
products is an isomorphism compatible with both projections, proving that
`Numerical.toPER` preserves binary products. This does not establish restriction
products in the category of partial numerical arrows.

`PERFiniteLimits` constructs a terminal PER and equalizers. Equalizer supports
are arbitrary subsets defined by agreement of the represented arrows. They
need not be recursively enumerable. The inherited representing function defines
the mediating morphism, whose uniqueness follows in the quotient hom-set.
Together with products these constructions give finite limits.

`PERImages.relationRegularEpi` assumes inclusion of PER relations and inclusion
of target support in source support. The relation inclusion supplies the
opposite support inclusion. The identity function represents the quotient,
and its coequalizer property is proved against every target PER.

For a morphism represented by `f`, the image PER has the source support and
identifies exactly those source elements with related outputs under `f`.
The quotient is a regular epimorphism; the induced morphism is monic.
For any kernel pair of the original morphism, cancellation of this monomorphism
gives a kernel pair of the quotient. Its coequalizer supplies
`hasCoequalizer_of_isKernelPair`.

## C. Local corrections

The source comment preceding `relationRegularEpi` was corrected grammatically.
Terminology changes are recorded in [EDITORIAL_REVIEW.md](EDITORIAL_REVIEW.md).
Imported-file edits are comment-only; their noncomment text was compared with
the original pinned sources.

## D. Consistency with the manuscript and status documentation

The constructions supply part of the numerical interpretation in
`sec:integration-numerical`. They do not establish a `Regular NumericalPER`
instance: the remaining requirement is stability under pullback. No
extensivity instance or identification of the imported typed arithmetic
category with the manuscript's numerical presentation is claimed.

## E. Requirements for the numerical application

Prove pullback stability of regular epimorphisms, construct the extensive
structure, and complete the numerical domain/subobject and recursion-category
interfaces. Then construct the syntactic Boolean presentation and interpret
theory extensions. Keep numeralwise provability distinct from a uniformly
quantified theorem throughout that comparison.

## F. Unchecked matters and assessment

The strongest confirmed limitation is the incomplete numerical instantiation
of the categorical theorem. This review found no additional concrete suspected
defect in the four modules. The arithmetic comparison and independent kernel
checking remain the most substantial unchecked parts. Acceptance of the full
formalization is therefore unresolved. Palomar Comparator, NanoDa, and con-ron
were not run.
