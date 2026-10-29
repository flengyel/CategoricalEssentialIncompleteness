/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.NumericalEnrichedGlobal
import CategoricalEssentialIncompleteness.NumericalEnrichedPredicates

/-!
# Global numerical predicates as PER subobjects

Evaluation of global total arrows, followed by the numerical functor to PERs,
preserves binary products. Evaluation at the unique point of the terminal type
identifies global predicates naturally with the full subobject lattices along
this functor. The induced domain embedding agrees with the numerical support
embedding.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace Numerical

/-- The PER-valued functor on global total numerical arrows. -/
def enrichedToPER : enrichedRestriction.GlobalTotal ⥤ NumericalPER :=
  globalTotalEvaluation ⋙ toPER

/-- The functor on global total arrows preserves binary products. -/
instance enrichedToPERPreservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) enrichedToPER :=
  inferInstanceAs
    (PreservesLimitsOfShape (Discrete WalkingPair) (globalTotalEvaluation ⋙ toPER))

/-- Evaluation of a global point of the totality pullback agrees with evaluation
of the underlying total arrow. -/
@[simp] theorem enrichedTotal_globalTotalPoint
    {X Y : enrichedRestriction.GlobalTotal} (f : X ⟶ Y) :
    enrichedTotalEquiv X.obj.obj Y.obj.obj
        (enrichedRestriction.globalTotalPoint f default) = globalTotalEvaluation.map f := by
  apply WideSubcategory.hom_ext
  exact ConcreteCategory.congr_hom (C := Type)
    (enrichedRestriction.globalTotalPoint_ι f) default

/-- A global predicate is determined by its value at the unique terminal point. -/
def enrichedPredicateSubobjectOrderIso (X : enrichedRestriction.GlobalTotal) :
    (enrichedRestriction.predicatesOnTotals enrichedProducts enrichedPredicates).obj X ≃o
      Subobject (enrichedToPER.obj X) where
  toFun p := (TypeCat.Hom.hom p) default
  invFun a := TypeCat.ofHom fun _ => a
  left_inv p := by
    apply ConcreteCategory.hom_ext (C := Type)
    intro t
    exact ConcreteCategory.congr_arg (C := Type) p (Subsingleton.elim _ _)
  right_inv _ := rfl
  map_rel_iff' := by
    intro p q
    change (⊤_ (Type) ⟶ predicates.obj (totalObject X.obj.obj)) at p q
    change p default ≤ q default ↔ ∀ t, p t ≤ q t
    constructor
    · intro h t
      simpa only [Subsingleton.elim t (default : ⊤_ (Type))] using h
    · intro h
      exact h default

@[simp] theorem enrichedPredicateSubobjectOrderIso_apply
    (X : enrichedRestriction.GlobalTotal)
    (p : (enrichedRestriction.predicatesOnTotals enrichedProducts enrichedPredicates).obj X) :
    enrichedPredicateSubobjectOrderIso X p = (TypeCat.Hom.hom p) default := rfl

/-- The global predicate functor is the full PER subobject functor along the
product-preserving numerical functor. -/
def enrichedPredicateSubobjectIdentification :
    SubobjectIdentification
      (enrichedRestriction.predicatesOnTotals enrichedProducts enrichedPredicates)
      enrichedToPER where
  app := enrichedPredicateSubobjectOrderIso
  naturality {X Y} f p := by
    change predicates.pull
      (enrichedTotalEquiv X.obj.obj Y.obj.obj
        (enrichedRestriction.globalTotalPoint f default)) ((TypeCat.Hom.hom p) default) =
      (Subobject.pullback (toPER.map (globalTotalEvaluation.map f))).obj
        ((TypeCat.Hom.hom p) default)
    rw [enrichedTotal_globalTotalPoint]
    rfl

/-- The subobject assigned to a global restriction domain is its numerical
support subobject. -/
theorem enriched_domainSubobject_apply {X : Numerical}
    (a : enrichedRestriction.GlobalDomain X) :
    enrichedRestriction.domainSubobject enrichedProducts enrichedPredicates
        enrichedPredicateEmbedding enrichedPredicateSubobjectIdentification X a =
      domainSubobject X (enrichedDomainEquiv X
        (((enrichedRestriction.globalDomainOrderIso X).symm a) default)) := by
  rw [enrichedRestriction.domainSubobject_apply]
  rfl

end Numerical
end CategoricalEssentialIncompleteness
