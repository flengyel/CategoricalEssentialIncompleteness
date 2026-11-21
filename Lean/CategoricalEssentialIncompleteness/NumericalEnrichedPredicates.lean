/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalEnrichedTotals
public import CategoricalEssentialIncompleteness.NumericalEnrichedDomains
public import CategoricalEssentialIncompleteness.NumericalPredicates

/-!
# Internal numerical predicates and domain embedding

All PER subobjects form the numerical predicate objects. Pullback acts pointwise on
families of total numerical morphisms. The restriction-domain equalizers embed
naturally into these objects by their support subobjects.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness
namespace Numerical

attribute [local instance] typeHomDistribLattice typeHomBoundedOrder

/-- The full numerical subobject lattice as an internal lattice in `Type`. -/
def enrichedPredicateLattice (X : Numerical) : InternalLattice Type :=
  typeLattice (predicates.obj (totalObject X))

/-- The predicate action on a total-morphism element and a subobject. -/
def enrichedPredicateAction (X Y : Numerical) :
    enrichedRestriction.totalObject X Y ⨯ predicates.obj (totalObject Y) ⟶
      predicates.obj (totalObject X) :=
  TypeCat.ofHom fun p =>
    predicates.pull (enrichedTotalEquiv X Y
      ((prod.fst : enrichedRestriction.totalObject X Y ⨯ predicates.obj (totalObject Y) ⟶
        enrichedRestriction.totalObject X Y) p))
      ((prod.snd : enrichedRestriction.totalObject X Y ⨯ predicates.obj (totalObject Y) ⟶
        predicates.obj (totalObject Y)) p)

/-- Pullback of predicate families along a family of total numerical morphisms. -/
def enrichedPredicatePull {T : Type} {X Y : Numerical}
    (f : T ⟶ enrichedRestriction.totalObject X Y) :
    BoundedLatticeHom (T ⟶ predicates.obj (totalObject Y))
      (T ⟶ predicates.obj (totalObject X)) where
  toFun a := TypeCat.ofHom fun t => predicates.pull (enrichedTotalEquiv X Y (f t)) (a t)
  map_inf' := by
    intro a b
    apply ConcreteCategory.hom_ext
    intro t
    exact (predicates.pull (enrichedTotalEquiv X Y (f t))).map_inf' (a t) (b t)
  map_sup' := by
    intro a b
    apply ConcreteCategory.hom_ext
    intro t
    exact (predicates.pull (enrichedTotalEquiv X Y (f t))).map_sup' (a t) (b t)
  map_bot' := by
    apply ConcreteCategory.hom_ext
    intro t
    exact (predicates.pull (enrichedTotalEquiv X Y (f t))).map_bot'
  map_top' := by
    apply ConcreteCategory.hom_ext
    intro t
    exact (predicates.pull (enrichedTotalEquiv X Y (f t))).map_top'

@[simp] theorem enrichedPredicatePull_apply {T : Type} {X Y : Numerical}
    (f : T ⟶ enrichedRestriction.totalObject X Y)
    (a : T ⟶ predicates.obj (totalObject Y)) (t : T) :
    enrichedPredicatePull f a t = predicates.pull (enrichedTotalEquiv X Y (f t)) (a t) := rfl

theorem enrichedPredicatePull_action {T : Type} {X Y : Numerical}
    (f : T ⟶ enrichedRestriction.totalObject X Y)
    (a : T ⟶ predicates.obj (totalObject Y)) :
    enrichedPredicatePull f a = prod.lift f a ≫ enrichedPredicateAction X Y := by
  apply ConcreteCategory.hom_ext
  intro t
  change predicates.pull (enrichedTotalEquiv X Y (f t)) (a t) =
    predicates.pull (enrichedTotalEquiv X Y ((prod.lift f a ≫ prod.fst) t))
      ((prod.lift f a ≫ prod.snd) t)
  rw [prod.lift_fst, prod.lift_snd]

/-- Full numerical subobject predicates with their internal total-morphism action. -/
def enrichedPredicates : InternalPredicates (enrichedRestriction.totalHom enrichedProducts) where
  lattice := enrichedPredicateLattice
  action := enrichedPredicateAction
  pull := enrichedPredicatePull
  pull_apply := enrichedPredicatePull_action
  pull_id {T X} a := by
    apply ConcreteCategory.hom_ext
    intro t
    change predicates.pull (enrichedTotalEquiv X X
      ((enrichedRestriction.totalHom enrichedProducts).identity X t)) (a t) = a t
    rw [enrichedTotal_identity, predicates.pull_id]
  pull_comp {T X Y Z} f g a := by
    apply ConcreteCategory.hom_ext
    intro t
    change predicates.pull (enrichedTotalEquiv X Z
      ((enrichedRestriction.totalHom enrichedProducts).comp f g t)) (a t) =
        predicates.pull (enrichedTotalEquiv X Y (f t))
          (predicates.pull (enrichedTotalEquiv Y Z (g t)) (a t))
    rw [enrichedTotal_comp]
    exact predicates.pull_comp _ _ _

@[simp] theorem enrichedPredicates_pull_apply {T : Type} {X Y : Numerical}
    (f : T ⟶ enrichedRestriction.totalObject X Y)
    (a : T ⟶ (enrichedPredicates.lattice Y).obj) (t : T) :
    enrichedPredicates.pull f a t =
      predicates.pull (enrichedTotalEquiv X Y (f t)) (a t) := rfl

/-- The numerical domain equalizer maps to its support subobject. -/
def enrichedDomainSubobjectHom (X : Numerical) :
    BoundedLatticeHom (enrichedRestriction.domainObject X)
      (predicates.obj (totalObject X)) :=
  (domainSubobjectHom X).comp (enrichedDomainOrderIso X : BoundedLatticeHom _ _)

@[simp] theorem enrichedDomainSubobjectHom_apply (X : Numerical)
    (e : enrichedRestriction.domainObject X) :
    enrichedDomainSubobjectHom X e = domainSubobjectHom X (enrichedDomainEquiv X e) := rfl

theorem enrichedDomainSubobjectHom_injective (X : Numerical) :
    Function.Injective (enrichedDomainSubobjectHom X) :=
  (domainSubobjectHom_injective X).comp (enrichedDomainEquiv X).injective

/-- The internal lattice map from the domain equalizer to all subobjects. -/
def enrichedDomainEmbeddingApp (X : Numerical) :
    InternalLatticeHom ((enrichedRestriction.domainPredicates enrichedProducts).lattice X)
      (enrichedPredicates.lattice X) :=
  typeLatticeHom (enrichedDomainSubobjectHom X)

theorem enrichedDomainEmbeddingApp_mono (X : Numerical) :
    Mono (enrichedDomainEmbeddingApp X).hom :=
  typeLatticeHom_mono _ (enrichedDomainSubobjectHom_injective X)

/-- The internal domain embedding is natural at every parameter type. -/
def enrichedPredicateEmbedding :
    InternalPredicateEmbedding (enrichedRestriction.domainPredicates enrichedProducts)
      enrichedPredicates where
  app := enrichedDomainEmbeddingApp
  mono := enrichedDomainEmbeddingApp_mono
  naturality {T X Y} f e := by
    apply ConcreteCategory.hom_ext
    intro t
    change predicates.pull (enrichedTotalEquiv X Y (f t))
      (domainSubobjectHom Y (enrichedDomainEquiv Y (e t))) =
        domainSubobjectHom X (enrichedDomainEquiv X
          (enrichedRestriction.domainInverse (f ≫ enrichedRestriction.totalι X Y) e t))
    rw [enrichedDomainInverse_apply]
    exact domainSubobject_naturality (enrichedTotalEquiv X Y (f t))
      (enrichedDomainEquiv Y (e t))

end Numerical
end CategoricalEssentialIncompleteness
