/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.GlobalSubobjects
import CategoricalEssentialIncompleteness.GlobalRepresentation
import CategoricalEssentialIncompleteness.BooleanDecisions

/-!
# Categorical essential incompleteness along `J`

The source of `J` is the ordinary total-arrow category of the enriched
restriction structure. Predicates are naturally identified with actual
subobjects along `J`, and the representing domains are actual restriction
idempotents of the underlying ordinary category. Representation is supplied
by the internal section.

The proof uses the restriction, lattice, predicate, and section data of a
definability algebra. The additional recursion and indexing structure is
not used. Binary-product preservation by `J` is retained in the principal
statement, although the quotient argument only uses the identification at `S`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe v u w v' u'
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace EnrichedRestriction
variable {V : Type u} [Category.{v} V] [HasFiniteLimits V] {O : Type w}
variable {H : InternalHom V O} (R : EnrichedRestriction H) [R.Zeros] [R.DomainLattices]
variable (products : R.Products) (P : InternalPredicates (R.totalHom products))
variable {C : Type u'} [Category.{v'} C] [Regular C] [FinitaryExtensive C]
variable (J : R.GlobalTotal ⥤ C)
variable (η : SubobjectIdentification (R.predicatesOnTotals products P) J)

/-- Both quotient bound fibers arise from ordinary restriction idempotents. -/
def RepresentedQuotientFibers
    (j : InternalPredicateEmbedding (R.domainPredicates products) P) (S : O)
    (q : BooleanPresentation (J.obj (R.totalGlobalObject S)))
    (r : BooleanQuotient q.algebra) : Prop :=
  ∃ a b : R.GlobalDomain S,
    (q.quotient r).positive = R.domainSubobject products P j η S a ∧
    (q.quotient r).negative = R.domainSubobject products P j η S b

/-- `prop:complete-extensions-and-decisions`, with global restriction domains
and the functor `J`. -/
theorem global_complete_extensions_and_decisions
    (j : InternalPredicateEmbedding (R.domainPredicates products) P) (S : O)
    (q : BooleanPresentation (J.obj (R.totalGlobalObject S))) :
    (∃ r : BooleanQuotient q.algebra,
      (q.quotient r).Consistent ∧ (q.quotient r).Complete ∧
      R.RepresentedQuotientFibers products P J η j S q r) ↔
    ∃ h : BooleanMorphism q.algebra (twoBooleanObject (C := C)),
      ∃ a : ComplementaryPair (R.GlobalDomain S),
        q.q ≫ h.hom =
          (representedPartition (R.domainSubobject products P j η S) a).characteristic :=
  complete_extensions_and_decisions _ (R.domainSubobject_injective products P j η S) q

variable (D : InternalDiagonalData (R.domainPredicates products) P)
variable (σ : D.RepresentationSection)
variable (hU : (𝟙 (R.globalObject D.U) : R.globalObject D.U ⟶ R.globalObject D.U) ≠ 0)
variable (q : BooleanPresentation (J.obj (R.totalGlobalObject D.S)))
variable (hpos : η.app (R.totalGlobalObject D.S) D.positive = q.positive)
variable (hneg : η.app (R.totalGlobalObject D.S) D.negative = q.negative)
variable (r : BooleanQuotient q.algebra)
include σ hU hpos hneg

/-- `thm:categorical-essential-incompleteness`: every consistent represented Boolean quotient
is incomplete. The domain and total-arrow comparisons are constructed, not assumed. -/
theorem categorical_essential_incompleteness
    (_preservesProducts : PreservesLimitsOfShape (Discrete WalkingPair) J)
    (consistent : (q.quotient r).Consistent)
    (represented : R.RepresentedQuotientFibers products P J η D.embedding D.S q r) :
    ¬ (q.quotient r).Complete := by
  obtain ⟨a, b, ha, hb⟩ := represented
  exact R.enriched_boolean_quotient_incomplete products D σ
    ((R.global_nontrivial_iff D.U).mp hU) (η.app (R.totalGlobalObject D.S))
    q hpos hneg r ((R.globalDomainOrderIso D.S).symm a) ((R.globalDomainOrderIso D.S).symm b)
    ((R.domainSubobject_apply products P D.embedding η a).symm.trans ha.symm)
    ((R.domainSubobject_apply products P D.embedding η b).symm.trans hb.symm) consistent

/-- The bound-copairing conclusion in `thm:categorical-essential-incompleteness`. -/
theorem categorical_boundCopair_not_regularEpi
    (preservesProducts : PreservesLimitsOfShape (Discrete WalkingPair) J)
    (consistent : (q.quotient r).Consistent)
    (represented : R.RepresentedQuotientFibers products P J η D.embedding D.S q r) :
    ¬ IsRegularEpi r.target.boundCopair := by
  intro h
  exact R.categorical_essential_incompleteness
    (products := products) (P := P) (J := J) (η := η) (D := D) (σ := σ)
    (hU := hU) (q := q) (hpos := hpos) (hneg := hneg) (r := r)
    preservesProducts consistent represented ((q.quotient r).complete_iff_regularEpi.mpr h)

omit r in
/-- No Boolean decision with represented complementary fibers exists for this presentation. -/
theorem global_no_boolean_decision
    (preservesProducts : PreservesLimitsOfShape (Discrete WalkingPair) J) :
    ¬ ∃ h : BooleanMorphism q.algebra (twoBooleanObject (C := C)),
      ∃ a : ComplementaryPair (R.GlobalDomain D.S),
        q.q ≫ h.hom =
          (representedPartition
            (R.domainSubobject products P D.embedding η D.S) a).characteristic := by
  intro decision
  obtain ⟨r, hc, ht, hr⟩ :=
    (R.global_complete_extensions_and_decisions products P J η D.embedding D.S q).mpr decision
  exact R.categorical_essential_incompleteness
    (products := products) (P := P) (J := J) (η := η) (D := D) (σ := σ)
    (hU := hU) (q := q) (hpos := hpos) (hneg := hneg) (r := r)
    preservesProducts hc hr ht

end EnrichedRestriction
end CategoricalEssentialIncompleteness
