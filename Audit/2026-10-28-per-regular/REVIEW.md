# PER regularity: source review

This review covers `PERPullbacks.lean` and `PERRegular.lean`. Compilation,
source hashes, and transitive axiom inspection are recorded separately.

## A. Correctness blockers

No concrete defect was found in these two constructions. The numerical
application still requires extensivity and the remaining recursion-category,
subobject, and arithmetic comparisons listed in `FORMALIZATION_STATUS.md`.

## B. Proof and hypotheses

The pullback PER restricts a product to pairs whose images are related in the
common target. Recursive coordinate projections commute with the cospan.
Pairing the representing functions of a cone supplies a mediating arrow;
the two projections determine it uniquely. The support may be an arbitrary
subset of the natural numbers.

For a regular epimorphism, the monomorphism in its previously constructed
image factorization is invertible by extremality. A function representing its
inverse is partial recursive and defined on the target support. It gives
preimages whose images are related to the original representatives.

Applying that function after the other cospan arrow, and pairing its value
with the input, gives a section of the image inclusion of the second pullback
projection. The function need not preserve the original source PER relation:
it represents a morphism into the image PER of the projection, whose relation
is determined by the second coordinate. This distinction is respected in the
construction. The image inclusion is consequently an isomorphism, proving
that the projection is a regular epimorphism.

Mathlib transports the property from these explicit pullbacks to arbitrary
pullback squares. Combined with finite limits and coequalizers of kernel pairs,
this supplies `NumericalPER.perRegular`.

## C. Local issues

Deprecated notation and linter suggestions encountered during compilation
were resolved. The new modules compile without warnings. Imported sources
were not edited.

## D. Consistency and dependency check

The proof of invertibility uses regular epimorphisms being extremal, not a
regular-category instance. The regularity instance is introduced only after
stability has been proved. No decidability or enumerability condition on PERs
or their supports is assumed. No computable selection of preimages is inferred
from surjectivity on equivalence classes alone.

The final stability result assumes only regularity of the original arrow.
The section hypothesis in the intermediate image criterion is discharged by
the explicitly constructed function.

## E. Remaining requirements

Construct PER coproducts and prove their pullback stability and disjointness,
then establish extensivity. Complete the numerical restriction products,
recursion/indexing structure, and natural bounded lattice comparison before
instantiating the categorical theorem. The syntax and provability comparison
must distinguish numeralwise proofs from a universally quantified theorem.

## F. Scope and assessment

The strongest confirmed limitation is the incomplete numerical instantiation,
not the regularity proof. No additional concrete suspected defect was found.
Arithmetic interpretation and independent kernel checking remain unverified.
The full formalization therefore remains incomplete. Palomar Comparator,
NanoDa, and con-ron were not run.

For the new prose, the supplied copy of Knuth, Larrabee, and Roberts,
*Mathematical Writing*, §1, was consulted, including the guidance on
self-contained statements, connected exposition, and unnecessary jargon.
The earlier editorial report retains its historical source-access status.
