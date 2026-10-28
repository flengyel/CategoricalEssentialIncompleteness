# Author-side formalization audit

This is a self-audit of the new global comparisons and categorical theorem,
against the indicated definitions and results in version 16 of *Definability
and incompleteness in recursion categories*. It is not independent peer review
or an independent kernel check. The manuscript was not edited.

## (A) Kill-shots / hard blockers

No correctness blocker was confirmed for the categorical statements proved in
this checkpoint. The anchor is `thm:categorical-essential-incompleteness`,
whose conclusion is that the consistent represented quotient “is incomplete.”
The Lean declaration `EnrichedRestriction.categorical_essential_incompleteness`
has an actual functor `J : GlobalTotal R → C`, regularity and extensivity,
product preservation, a natural subobject identification, the internal section,
ordinary identity unequal to zero, and the two represented quotient fibers.
Evidence: **structural_argument**, compiled proof terms, and the retained
principal-statement and axiom logs. The previous global-comparison gap is
resolved by the six new modules, not by an additional representation premise.

## (B) Major weaknesses

The remaining mathematical gap in the requested formalization is numerical.
Anchors: `thm:integration-essential-equivalence` (LaTeX label at line 1196),
`prop:numerical-boolean-extensions` (label at line 1252), and
`cor:arithmetic-representation-incompleteness` (label at line 1315). The numerical
theorem compares categorical representation with being “strongly definable
numeralwise in T”; the quotient proposition compares represented bound fibers
with c.e. axiomatizability. These comparisons are absent from the Lean
development. Failure mode of any claim that the complete numerical program is
formalized: **unproved**. Evidence: **absence_in_text** in the project modules
and declaration audit. Severity: major remaining formalization gap; repairable
by constructing the numerical/PER and syntax/provability comparisons. This is
not a claim that the manuscript's numerical statements are false.

The imported typed arithmetic program category is not identified with the
numerical category or its PER presentation. Objects, arrow equality,
restriction domains, numeral substitution, and theorem/refutation fibers must
be compared explicitly. Compiling the imported evaluator does not supply these
comparisons. Numeralwise instance proofs remain distinct from a proof of one
universally quantified sentence.

## (C) Minor issues

Anchor: `thm:categorical-essential-incompleteness`, the hypothesis that `J`
“preserve binary products.” Failure mode: **unused_hypothesis** in the quotient
proof, not a failure of its conclusion. The printed hypothesis is retained in
the Lean principal statement. Once the internal obstruction and predicate
identification are available, the proof only needs the component at `S`.
Evidence: **derivation**, namely the call to the proved enriched quotient
theorem. Severity: minor scope observation; no correction is required.

Definition `def:generalized-definability-algebra` includes additional recursion
and indexing data. The Lean theorem uses the restriction, product, zero,
lattice, predicate, and section part of that definition. The additional data
are unused in this argument. A single record bundling the entire algebra and
a comparison with Mathlib's bundled enriched-category interface are not
provided. The theorem does not introduce extra mathematical hypotheses to
replace those omitted, unused fields.

All six new modules compile without warnings. The two existing imported linter
warnings remain. Full verification passes all 113 audits, retaining all 83
previous checks. The scan of all twenty-four project Lean files finds no
proof-hole or new-axiom declarations. Toolchain and dependency pins are unchanged.

## (D) Cross-section consistency failures

No new inconsistency was confirmed. The relevant comparisons have the following
typed actions and proved laws:

| Construction | Object and arrow action | Laws checked |
| --- | --- | --- |
| Global total comparison | Same object labels; a point `1 → T(X,Y)` maps to its inclusion in `H(X,Y)`, with totality proved. | Identity, composition, inverse functor, unit, counit, triangle identity, and binary-product preservation. |
| Global domain comparison | A point `1 → E_X` maps to its restriction-fixed endomorphism in `K₀`. | Bijection, lattice order `e >> d = e`, meet as composition, identity/zero bounds, and compatibility with partial inverse image. |
| Global representation | The external substitution includes the chosen-product isomorphism. | Projection and product-naturality equations; equivalence of both internal and external representation equations; representatives supplied by the internal section. |
| Predicate identification | For `f : X → Y`, predicates move from `P(Y)` to `P(X)`, and subobjects move from `Sub(JY)` to `Sub(JX)`. | Identity and contravariant composition; natural isomorphism of presheaves; naturality and injectivity of the domain-to-subobject map. |

The variance check for a category containing only a nonidentity arrow `X → Y`
requires no arrow `Y → X`: both predicate actions reverse the displayed
direction. Naturality is proved for every relevant total arrow, not merely for
isomorphisms. The domain inverse-image comparison also applies to partial
arrows. Arrow equality is categorical equality in the underlying category;
no equality of program codes or arithmetic formulas is substituted for it.

The actual total-arrow category is the wide subcategory of the existing
`RestrictionCategory.isTotal` property. This avoids imposing the extra
`PCategory` presentation required by the older `TotalSubcategory` abbreviation.
The new `GlobalDomain` has the defining equation `rst e = e`; its order and
operations are proved to be the restriction-domain ones. No identification
with the older `DomSemilattice` type is asserted without a `PCategory` comparison.

The sorts `E` and `P` and objects `U` and `S` remain separate. Complementarity
is derived for the two quotient representatives from consistency and assumed
completeness. The original distinguished predicates need not lie in the image
of `j_S`. The internal factorization at `Sep` remains a proof at that parameter
object; absence of global separators is not used to infer it.

## (E) Acceptance conditions, non-negotiable

1. Construct the total-arrow comparison as functors with inverse and product
   laws. Met by `globalTotalEquivalence` and its product-preservation theorem.
   Failure would block the claimed global comparison.
2. Identify global domain points with genuine restriction idempotents, including
   order, bounds, meet, and inverse image. Met by `GlobalDomains.lean`.
   Failure would block the ordinary-domain statement.
3. Derive external representatives from the internal section through the
   actual product comparison. Met by `global_represents_iff` and
   `global_representation`. Failure would block the representation bridge.
4. Supply actual predicate functors and the natural subobject comparison along
   `J`. Met by `presheafIso` and `domainSubobject_naturality`.
   Failure would block the statement along `J`.
5. Prove both categorical incompleteness conclusions for genuine Boolean
   quotients with the stated hypotheses. Met by `CategoricalTheorem.lean`.
6. Construct the numerical/PER and provability comparisons before claiming
   arithmetic essential incompleteness. Not met; that completion claim is excluded.
7. Retain every previous audit, dependency pin, and imported-source hash.
   Met by the full verifier. Independent checker status remains separate.

## (F) Not checked / uncertainty log

Palomar Comparator, NanoDa, and con-ron were not run. No numerical model
instance or equivalence with the imported typed arithmetic category was proved.
No whole-manuscript correctness or novelty judgment is made. The previously
recorded limitation on accessing the complete *Mathematical Writing* source
remains; no complete source-based editorial-compliance claim is made.

The strongest confirmed blocker to completing the requested formalization is
the numerical comparison. No additional categorical blocker is confirmed or
asserted on suspicion. The most important unchecked item is the relationship
between the numerical/PER construction and arithmetic syntax and provability.
The compiled categorical conclusions do not depend on unavailable editorial
material; an assessment of the complete manuscript and numerical program does.
Final recommendation for the complete formalization: **unknown** pending those
remaining constructions and independent checks.
