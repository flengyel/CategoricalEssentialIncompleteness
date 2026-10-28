# Author-side formalization audit

This audit compares the enriched restriction construction with version 16 of
*Definability and incompleteness in recursion categories*. It is a self-audit
of scope and correctness, not an independent referee or kernel check.

## (A) Kill-shots / hard blockers

No correctness blocker was confirmed for the statements proved from the
specified enriched restriction, lattice, predicate, and representation data.
The domain objects are the actual fixed-point equalizers of restriction, and
the total-arrow objects are the actual pullbacks of restriction along identity.
Their generalized-point equivalences, total-arrow operations, and domain
inverse image are constructed. Evidence: **structural_argument** and compiled
Lean statements and proof terms.

The full manuscript theorem is not yet claimed. The remaining global
comparison has not been assembled with the functor `J` and its natural
subobject identification. The new quotient result instead takes the component
identification at `S` explicitly. A claim that the fully packaged theorem is
complete would be **unproved**; evidence: **absence_in_text**. This is a
formalization gap, not a counterexample to the manuscript.

## (B) Major weaknesses

`EnrichedRestriction` specifies the category and restriction equations on
generalized arrows. It instantiates the existing `RestrictionCategory` API at
every parameter. It is not an identification with Mathlib's bundled enriched
category interface, and the manuscript's global recursion and indexing data
have not been bundled with it. These latter structures are not premises of the
diagonal calculation once the representation section is supplied.

The comparison with ordinary global total arrows, global restriction domains,
and the external predicate functor remains to be constructed. In particular,
the existing `DomSemilattice` presentation requires additional `PCategory`
structure; no comparison with that presentation is silently inferred.

The numerical/PER and arithmetic comparisons remain unproved. The typed
arithmetic program category is not identified with the manuscript's numerical
presentation. Numeralwise proofs of instances must remain distinct from a
proof of one universally quantified sentence.

## (C) Minor issues

The four new modules compile without warnings. The two existing imported
linter warnings remain. Verification evidence records the full build, all
83 axiom audits, and the source-hole scan for all eighteen project Lean files.
The previous 62 audits are retained. No imported source or dependency pin
was changed.

## (D) Cross-section consistency failures

No new inconsistency was confirmed. The restriction laws R1–R4 use Lean's
diagrammatic composition convention. `domainPointsEquiv` and `totalPointsEquiv`
prove the exact generalized-point descriptions of the finite-limit objects.
Restriction products have the partial projection equations. The restriction
of a pairing is derived from those equations and R3, and total pairings follow.
All category and binary-product laws for the total hom-objects are proved by
their monic inclusions; they are not assumed for partial arrows.

`DomainLattices` specifies the manuscript's extra bounded distributive lattice
structure on the actual equalizers. Meet is tied to composition, top to
identity, and bottom to zero. `domain_le_iff` proves that its order is the
restriction-domain order. Join stability is assumed for partial inverse image
as in the manuscript; meet preservation and preservation of bounds by total
inverse image are proved from restriction and zero laws. The partial action
is a morphism on `H(X,Y) × E_Y`; the total action is its restriction along
the totality inclusion. No range or complement hypotheses from the imported
Rice–Shapiro decision results are introduced.

The internal separator proof is instantiated with these constructed objects
and actions. The representation section supplies the varying representative
at `Sep`. The factorization through `Z_U` is proved before passing to global
points. `domain_bounds_ne` connects the inequality of the original enriched
identity and zero with inequality of the global domain bounds.

For genuine Boolean quotients, consistency and assumed completeness are
reflected through the monic bounded lattice embedding, making the two
representing domains complementary. Preservation of bounds gives the two
separator inequalities. The resulting global point of `Sep` contradicts the
enriched nonexistence result. The bound-copairing conclusion uses the proved
Boolean-presentation lemma. The component subobject identification is an
explicit order isomorphism; it is not assumed to be supplied by an unconstructed
comparison with `J`.

The sorts `E` and `P` and the objects `U` and `S` remain separate. Neither
complements for every restriction domain nor representation of the original
distinguished predicates through `j_S` is assumed.

## (E) Acceptance conditions, non-negotiable

1. Construct the actual restriction-domain equalizers and totality pullbacks,
   with their generalized-point descriptions. Met.
2. Derive internal total-arrow composition and binary products from the
   enriched restriction-product equations. Met.
3. Construct domain inverse image and derive the required laws without adding
   complement or range hypotheses. Met, with the manuscript's explicit lattice
   and join-stability structure.
4. Instantiate the separator factorization and Boolean-quotient obstruction
   from the internal representation section. Met; the quotient theorem takes
   the component subobject identification at `S` explicitly.
5. Complete the global comparison and package the theorem with `J` and its
   natural identification. Not met.
6. Prove the numerical/PER and provability comparisons before claiming
   arithmetic essential incompleteness. Not met.
7. Retain all dependency pins, imported provenance, and previous audits. Met.
   Independent checker status remains separate.

## (F) Not checked / uncertainty log

Palomar Comparator, NanoDa, and con-ron were not run. No literature or novelty
claim is made, and the manuscript was not edited. The previously recorded
limitation on retrieving the complete *Mathematical Writing* source remains;
no complete source-based editorial-compliance claim is made.

The next unresolved construction is the global total-arrow and predicate
comparison, including the natural subobject identification along `J`.
