# Numerical Boolean arrows and complemented subobjects: source review

This review covers `ComplementedSubobjects`, `NumericalBooleanObject`,
`NumericalBooleanArrows`, `NumericalBooleanFibers`, and
`NumericalComplementedSubobjects`. All five modules were read in full, with
the definitions and categorical comparison results used by their proofs.
The manuscript comparison concerns `lem:integration-numerical-subobjects`
in version 16. The preceding checkpoint is
`f51ca8e82ba08603f206f51f1ec1b37ad047e45d`.

## A. Correctness findings

No concrete defect was found in the five modules. They establish the
correspondence between total recursive Boolean functions and arrows from
the equality PER on the natural numbers to the Boolean PER. They identify
the fibers of these arrows with recursive support inclusions, and prove
that these are precisely the complemented subobjects of that equality PER.
Together with the preceding natural domain embedding, support order, and
pullback results, these declarations supply every assertion of
`lem:integration-numerical-subobjects`.

## B. Constructions and hypotheses

`ComplementedSubobjects` works in a regular finitely extensive category.
The two inclusions into the coproduct of terminal objects are complementary:
their copairing is the identity, hence is both monic and a regular epimorphism.
The corresponding subobjects therefore have meet bottom and join top.
The bounded lattice pullback map preserves this complementarity along any
arrow. Conversely, the existing characteristic-arrow construction realizes
every complemented subobject as an upper fiber. No regular-epimorphism
hypothesis is imposed on the arrow whose fibers are taken.

`NumericalBooleanObject` defines the Boolean PER as equality restricted to
the support `{0, 1}`. Recursive tuple coding gives mutually inverse arrows
between this object and the explicit coproduct of two terminal PERs. The
inverse equations hold as equalities of PER morphisms; the equation on the
coproduct need not be an equality of representing numerical functions.
The coproduct universal property then supplies the isomorphism from the
chosen object `1 + 1`. Both constant-point equations are proved. Equality
on each singleton support is terminal, and the associated isomorphism
identifies a Boolean point with its singleton support subobject.

`NumericalBooleanArrows` maps a total recursive Boolean function to the
arrow represented by its numerical values zero and one. Equality of these
arrows is proved equivalent to equality of the Boolean functions. For an
arbitrary arrow, a representing partial recursive function is defined at
every natural number because the source support is all of `ℕ`. Extracting
its value gives a total recursive numerical function. Its values belong to
`{0, 1}`, so comparison with one gives a recursive Boolean function denoting
the original arrow. Injectivity and surjectivity yield `booleanArrowEquiv`.

`NumericalBooleanFibers` uses the singleton-point comparison and the
categorical pullback theorem for support inclusions. Thus the fiber over a
Boolean value is the subobject represented by the corresponding inverse
image. Equality with a fixed Boolean value is a recursive predicate. In the
opposite direction, the characteristic function of a recursive predicate
has the required upper fiber. Both directions are stated for categorical
subobject equality, not just equality of supports.

`NumericalComplementedSubobjects` transports the general characteristic-arrow
result through the explicit Boolean isomorphism. The fiber characterization
then proves that every complemented subobject of `D_ℕ` is a recursive
support inclusion. The previously constructed complementary restriction
domains for a recursive set identify these subobjects with the images of
complemented numerical domains. Injectivity of the domain embedding also
proves that the embedding reflects existence of a complement on `ℕ`.

## C. Local issues

The full verifier passed after the five source modules were complete: the
build finished with 1,936 jobs, and all 273 axiom audits passed, retaining
the preceding 247 declarations. The five new modules produced no warnings;
the two pre-existing imported warnings remain. Dependency pins, imported
sources, and manuscript files are unchanged. The verification logs and
the scan of the 51 project Lean files are recorded separately in this
directory.

The mathematical comments state the constructions and hypotheses directly.
The distinction between a representing partial recursive function and its
morphism class is retained where the inverse equations and arrow
correspondence depend on it. No terminology or prose defect requiring a
source change was found. Section 1 of the supplied *Mathematical Writing*
was consulted for self-contained statements, connected exposition, and
unnecessary jargon. No whole-manuscript editorial judgment is made here.

## D. Consistency and dependency check

The generic classification quantifies over all subobjects. Its numerical
specialization derives the recursive support representation from
complementarity; it does not assume that arbitrary PER subobjects are
support inclusions. The previously established restriction of the support
join theorem to c.e. sets is preserved.

The finite Boolean object lies in the PER category. It is not asserted to
be an object of the numerical restriction category, whose objects have
infinite recursive carriers. The numerical domain comparison is taken at
the object `nat`, where the carrier is all of `ℕ`.

The two Boolean values remain distinguished by the point equations, with
`false` represented by zero and `true` by one. The fiber comparisons are
compatible with diagrammatic composition. The final domain theorem
reflects existence of a complement by first representing the complemented
subobject; it does not infer this existential conclusion merely from
reflection of complementarity for a specified pair.

No new unproved axiom or premise restating a desired conclusion occurs in
the reviewed constructions. No imported source or manuscript file was
changed in this checkpoint.

## E. Remaining requirements

The next numerical construction is the restriction-product structure,
followed by recursion and indexing. The enriched structure and its
compatibility with the ordinary numerical category still require explicit
construction. Effective syntax, numeral substitution, the Lindenbaum Boolean
presentation, and theory-extension quotients remain necessary for the
arithmetic interpretation.

The new Boolean classification does not itself construct those syntactic
objects or establish the arithmetic representation equations. Numeralwise
provability of individual instances must remain distinct from provability
of a single universally quantified sentence.

## F. Scope and assessment

The numerical subobject lemma is established by the new declarations and
the preceding domain and subobject constructions. The numerical
instantiation of the categorical essential-incompleteness theorem and its
arithmetic interpretation remain incomplete. No additional suspected
mathematical defect was identified in the reviewed modules. This review did
not check other manuscript claims or new literature references. Palomar
Comparator, NanoDa, and con-ron were not run.
