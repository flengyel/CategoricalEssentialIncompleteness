# Author-side numerical formalization audit

This self-audit covers the seven new numerical modules and their correspondence
with the numerical interpretation in version 16 of *Definability and
incompleteness in recursion categories*. It is not independent peer review.
The manuscript was not edited.

## (A) Kill-shots / hard blockers

No correctness blocker was confirmed for the statements proved in this
checkpoint. The object class, partiality, tracker equality, and genuine
subobject constructions match the clauses being formalized. Evidence:
**structural_argument**, compiled proof terms, the principal-statement log,
and the transitive axiom audit.

The absence-of-separator theorem requires disjoint distinguished supports.
The definition of recursive inseparability includes disjointness. Neither
distinguished support is assumed c.e. This is the support statement underlying
part (ii) of `thm:integration-essential-equivalence`, not an arithmetic
instantiation of that theorem.

## (B) Major weaknesses

1. The numerical model is not yet a complete instance of the categorical
   theorem. Anchors: `sec:integration-numerical`, LaTeX lines 838–845
   (“binary products remain in this category”); lines 866–868 (“preserves
   binary products”); line 885 (“regular and extensive”). Failure mode of
   a complete-model claim: **unproved**. Evidence: **absence_in_text** in the
   new modules, which construct restriction and category laws, a full faithful
   functor, and particular support pullbacks, but not the remaining products,
   finite limits, regular images, and extensive coproducts. Severity: major
   remaining formalization gap. Repairable by those constructions. No claim
   that the manuscript's assertions are false is made.

2. The syntax/provability and theory-extension comparisons remain absent.
   Anchors: `prop:integration-arbitrary-adequacy`, the clause “strongly defines
   A numeralwise in T”; `thm:integration-essential-equivalence` (label at
   line 1196); `prop:numerical-boolean-extensions` (label at line 1252);
   `cor:arithmetic-representation-incompleteness` (label at line 1315).
   Failure mode of an arithmetic-essential-incompleteness claim:
   **unproved**. Evidence: **absence_in_text** in the project modules and
   declaration audit. Downstream obligations include effective syntax,
   numeral substitution, theorem/refutation supports, the Lindenbaum Boolean
   presentation, regular quotient maps for extensions, and the representation
   section. Severity: major remaining gap; repairable. The existing typed
   arithmetic program category is not identified with the numerical category.

## (C) Minor issues

No additional minor correctness defect was confirmed.

The numerical domain-to-subobject map is currently an order embedding.
The c.e. join theorem proves the full least-upper-bound property among all
subobjects, and the inverse-image theorem proves a full pullback universal
property. These do not by themselves supply all the typeclass instances needed
to package the map as the manuscript's natural bounded lattice homomorphism.

Anchor: `lem:integration-numerical-subobjects`, lines 891–892, “injective
bounded lattice homomorphisms.” The packaging and the lemma's Boolean-fiber
and complemented-subobject assertions remain **unproved** in the numerical
model. Evidence: **absence_in_text**; these are recorded as remaining parts of
that lemma rather than reported as a defect in the proved components.

## (D) Cross-section consistency failures

No new inconsistency was confirmed.

| Construction | Types and equality | Laws or comparison proved |
| --- | --- | --- |
| Numerical arrows | Infinite recursive subsets of ℕ; partial recursive functions undefined outside the source. Equality is equality of partial functions. | Category laws, all four restriction laws, zero morphisms, ordinary nontriviality, and totality exactly on the source. |
| Domain supports | Restriction-fixed endomorphisms map to c.e. subsets of their source. | Order isomorphism; restriction-composition order; intersection, union, zero and identity; partial inverse image. |
| PER arrows | Arbitrary symmetric transitive relations on ℕ; partial recursive trackers total on supported inputs. | Tracker equivalence, compatibility of composition, quotient category laws, and supported-value equality for equality PERs. |
| Numerical functor | `J : Numerical.Total → NumericalPER`; an object maps to its equality PER and an arrow to its tracker class. | Identity, composition, fullness, and faithfulness. Product preservation is not claimed. |
| Support subobjects | `D_A → D_X` for arbitrary `A ⊆ X`. | Monicity, order and equality reflection, pullback existence with arbitrary PER test objects, and uniqueness. |
| C.e. union | `D_(A ∪ B) → D_X`, with c.e. hypotheses on both supports. | Factorization through every common categorical upper bound, using partial-recursive dovetailing. |
| Separators | Complementary numerical restriction domains and inequalities of actual PER subobjects. | Equivalence with recursive separating sets, and its negation for disjoint distinguished supports. |

The inverse-image direction is from predicates on the target to predicates on
the source. The construction needs no reverse arrow in the two-object,
one-arrow test category. Its universal property quantifies over arbitrary PER
sources, not just equality PERs or numerical objects.

The total-arrow functor does not equate distinct tracker codes. The source
uses extensional partial functions; the target quotients by related outputs
on supported inputs. Fullness explicitly restricts a tracker to the recursive
source before returning a source arrow.

The union proof uses the c.e. hypotheses to obtain partial-recursive support
tests and their dovetailing. It proves a least upper bound against arbitrary
categorical subobjects, not just against other support inclusions. It does not
identify the full subobject lattice with a powerset.

No total-function semantics is substituted for partial arrows. The partial
inverse-image support formula contains an actual convergent output witness.
No complement is assumed for every numerical restriction idempotent.

## (E) Acceptance conditions, non-negotiable

1. Construct the numerical category with the manuscript's object class,
   extensional partial arrows, and restriction laws. Met by
   `NumericalCategory.lean); failure would block the numerical-category claim.
2. Identify genuine restriction domains with c.e. supports, including the
   lattice and inverse image. Met by `NumericalDomains.lean); failure would
   block the recursive/complemented comparison.
3. Construct arbitrary PERs with quotient tracker arrows and prove the functor
   full and faithful. Met by `NumericalPER.lean` and
   `NumericalEmbedding.lean`; failure would block the comparison along `J`.
4. Use genuine subobjects and full universal properties. Met by
   `inverse_isPullback` and `enumerable_union_isLUB`; failure would block the
   support-subobject claims.
5. Prove the numerical separator equivalence with disjointness explicit and
   without c.e. hypotheses on distinguished supports. Met by
   `no_separator_iff_recursively_inseparable`.
6. Construct the remaining numerical/PER structure and provability comparisons
   before claiming the complete numerical or arithmetic theorem. Not met;
   those completion claims are excluded.
7. Retain previous audits, dependency pins, and imported-source hashes.
   Met: full verification passes 152 audits, retaining all previous 113.

## (F) Not checked / uncertainty log

Palomar Comparator, NanoDa, and con-ron were not run. No equivalence with the
imported typed arithmetic program category, modest sets, or exact completion
was proved. No numerical product-preservation, regularity, or extensivity
instance is claimed. No whole-manuscript correctness or novelty judgment is
made.

The prose check concerns source comments and the repository's formalization
status. The previously recorded inability to consult the complete
*Mathematical Writing* source remains a limitation; no complete source-based
editorial-compliance claim is made. The manuscript was unchanged.

The strongest confirmed blocker to complete numerical formalization is the
remaining numerical/PER structure followed by the syntax/provability bridge.
No further suspected correctness blocker is asserted without evidence.
The most important unchecked item is the full numerical instantiation of
the already proved categorical theorem. The current compiled statements do
not depend on unavailable editorial material. Final recommendation for a
claim of complete numerical formalization: **unknown** pending the remaining
constructions; the present checkpoint makes no such claim.
