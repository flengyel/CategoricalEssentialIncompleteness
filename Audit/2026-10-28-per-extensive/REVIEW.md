# PER finite coproducts and extensivity: source review

This review covers `PERCoproducts`, `PERCoproductSquares`,
`PERCoproductDecomposition`, and `PERExtensive`. Compilation and axiom inspection
are recorded separately.

## A. Correctness blockers

No concrete defect was found in these constructions. The numerical application
still requires the domain embedding as a natural bounded lattice homomorphism,
restriction products and recursion, and the arithmetic comparisons.

## B. Constructions and hypotheses

The coproduct of two PERs uses codes `Nat.pair 0 n` and `Nat.pair 1 n`.
Related codes lie in the same summand and have related second coordinates.
Recursive injection and copairing functions prove the universal property;
both injections are monic. The empty PER is initial, giving finite coproducts.

For a map of coproducts into the coproduct of terminal objects, the two
commuting injection equations determine the map. The output's first coordinate
determines the source summand. Recursive decoding supplies a mediating arrow
for each injection square; monicity proves uniqueness.

For an arbitrary arrow represented by `f`, the copairing of the projections
from the pullbacks along the two target injections has an explicit inverse.
On input `n`, it evaluates `f`, retains its first coordinate, and pairs `n`
with its second coordinate. The result belongs to the corresponding pullback
support. Relation preservation follows from the relation preserved by `f`.
Both inverse equations hold as equalities of morphism classes; the reverse
equation does not assert equality of numerical representatives.

Transport along the universal-property isomorphisms gives the decomposition
for Mathlib's chosen pullbacks. The injection squares and decomposition establish
the van Kampen property for the coproduct of terminal objects. Mathlib's
characterization yields `FinitaryExtensive NumericalPER`. The pullback of the
two coproduct injections is initial.

## C. Local issues

The four new modules compile without warnings. The final build used newly
compiled artifacts for all four modules after development was complete.
No imported Lean file was changed.

## D. Consistency and dependency check

The constructions allow arbitrary PERs and supports. No enumerability or
decidability assumption on a support is introduced. The required computation
is evaluation of a supplied partial recursive function, followed by recursive
pairing and decoding. Decomposition is proved by its inverse equations rather
than assumed as a field. The extensivity instance is declared only after
these properties are proved.

Regularity remains the separately proved instance. Finite extensivity supplies
the categorical theorem's `FinitaryExtensive` hypothesis; no arbitrary infinite
coproduct assertion is made.

## E. Remaining requirements

Prove preservation of bounds, meets, and joins by the numerical domain map,
and combine this with its inverse-image comparison. Construct the numerical
restriction products and recursion/indexing data. The syntactic Boolean
presentation, theory-extension quotients, and arithmetic representation
comparison remain open. Numeralwise provability must remain distinct from
provability of a universally quantified sentence.

## F. Scope and assessment

The strongest confirmed limitation is the incomplete numerical instantiation
of the categorical theorem. No additional concrete suspected defect was found
in these four modules. The arithmetic interpretation and independent kernel
checking remain unverified. The full formalization is incomplete. Palomar
Comparator, NanoDa, and con-ron were not run.
