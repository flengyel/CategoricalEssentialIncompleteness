/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalEnriched
public import CategoricalEssentialIncompleteness.NumericalDomainReindexing
public import CategoricalEssentialIncompleteness.TypeLattices
public import Mathlib.CategoryTheory.Limits.Types.Equalizers

/-!
# The internal lattice of numerical domains

The fixed-point equalizer of numerical restriction is equivalent to the
numerical domain lattice. Families of equalizer elements therefore have
pointwise bounded distributive lattice operations at every parameter type.
Restriction inverse image acts pointwise and preserves binary joins.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace Numerical

/-- Elements of the domain equalizer are numerical restriction domains. -/
def enrichedDomainEquiv (X : Numerical) : enrichedRestriction.domainObject X ≃ Domain X :=
  (Types.equalizerIso (enrichedRestriction.restriction X X)
    (𝟙 (enrichedHom.hom X X))).toEquiv.trans
    { toFun e := ⟨e.val, e.property⟩
      invFun e := ⟨e.hom, e.isDomain⟩
      left_inv _ := rfl
      right_inv _ := rfl }

@[simp] theorem enrichedDomainEquiv_hom (X : Numerical)
    (e : enrichedRestriction.domainObject X) :
    (enrichedDomainEquiv X e).hom = enrichedRestriction.domainι X e := rfl

/-- Generalized equalizer elements are arbitrary families of numerical domains. -/
def enrichedDomainFamilyEquiv (T : Type) (X : Numerical) :
    (T ⟶ enrichedRestriction.domainObject X) ≃ (T → Domain X) where
  toFun e t := enrichedDomainEquiv X (e t)
  invFun e := ↾fun t ↦ (enrichedDomainEquiv X).symm (e t)
  left_inv e := by
    apply ConcreteCategory.hom_ext
    intro t
    exact (enrichedDomainEquiv X).symm_apply_apply (e t)
  right_inv e := by funext t; exact (enrichedDomainEquiv X).apply_symm_apply (e t)

@[simp] theorem enrichedDomainFamilyEquiv_apply {T : Type} {X : Numerical}
    (e : T ⟶ enrichedRestriction.domainObject X) (t : T) :
    enrichedDomainFamilyEquiv T X e t = enrichedDomainEquiv X (e t) := rfl

/-- Reindexing a family is ordinary precomposition. -/
theorem enrichedDomainFamilyEquiv_precomp {T T' : Type} {X : Numerical}
    (k : T' ⟶ T) (e : T ⟶ enrichedRestriction.domainObject X) :
    enrichedDomainFamilyEquiv T' X (k ≫ e) =
      fun t ↦ enrichedDomainFamilyEquiv T X e (k t) := rfl

instance enrichedDomainDistribLattice (X : Numerical) :
    DistribLattice (enrichedRestriction.domainObject X) :=
  (enrichedDomainEquiv X).distribLattice

instance enrichedDomainBoundedOrder (X : Numerical) :
    BoundedOrder (enrichedRestriction.domainObject X) where
  top := (enrichedDomainEquiv X).symm ⊤
  bot := (enrichedDomainEquiv X).symm ⊥
  le_top e := by
    change enrichedDomainEquiv X e ≤ enrichedDomainEquiv X ((enrichedDomainEquiv X).symm ⊤)
    rw [Equiv.apply_symm_apply]
    exact le_top
  bot_le e := by
    change enrichedDomainEquiv X ((enrichedDomainEquiv X).symm ⊥) ≤ enrichedDomainEquiv X e
    rw [Equiv.apply_symm_apply]
    exact bot_le

/-- The equalizer comparison preserves the numerical lattice order. -/
def enrichedDomainOrderIso (X : Numerical) :
    enrichedRestriction.domainObject X ≃o Domain X where
  toEquiv := enrichedDomainEquiv X
  map_rel_iff' := Iff.rfl

attribute [local instance] typeHomDistribLattice typeHomBoundedOrder

/-- The generalized-element comparison is an order isomorphism at every parameter type. -/
def enrichedDomainFamilyOrderIso (T : Type) (X : Numerical) :
    (T ⟶ enrichedRestriction.domainObject X) ≃o (T → Domain X) where
  toEquiv := enrichedDomainFamilyEquiv T X
  map_rel_iff' := Iff.rfl

@[simp] theorem enrichedDomainFamilyEquiv_inf {T : Type} {X : Numerical}
    (a b : T ⟶ enrichedRestriction.domainObject X) :
    enrichedDomainFamilyEquiv T X (a ⊓ b) =
      enrichedDomainFamilyEquiv T X a ⊓ enrichedDomainFamilyEquiv T X b :=
  (enrichedDomainFamilyOrderIso T X).map_inf a b

@[simp] theorem enrichedDomainFamilyEquiv_sup {T : Type} {X : Numerical}
    (a b : T ⟶ enrichedRestriction.domainObject X) :
    enrichedDomainFamilyEquiv T X (a ⊔ b) =
      enrichedDomainFamilyEquiv T X a ⊔ enrichedDomainFamilyEquiv T X b :=
  (enrichedDomainFamilyOrderIso T X).map_sup a b

@[simp] theorem enrichedDomainFamilyEquiv_top (T : Type) (X : Numerical) :
    enrichedDomainFamilyEquiv T X ⊤ = ⊤ := (enrichedDomainFamilyOrderIso T X).map_top

@[simp] theorem enrichedDomainFamilyEquiv_bot (T : Type) (X : Numerical) :
    enrichedDomainFamilyEquiv T X ⊥ = ⊥ := (enrichedDomainFamilyOrderIso T X).map_bot

/-- The internal restriction inverse image evaluates to the numerical inverse image. -/
theorem enrichedDomainInverse_apply {T : Type} {X Y : Numerical}
    (f : T ⟶ enrichedHom.hom X Y) (e : T ⟶ enrichedRestriction.domainObject Y) (t : T) :
    enrichedDomainEquiv X (enrichedRestriction.domainInverse f e t) =
      domainInverse (f t) (enrichedDomainEquiv Y (e t)) := by
  apply Domain.ext
  change enrichedRestriction.domainι X (enrichedRestriction.domainInverse f e t) =
    restrict (f t ≫ enrichedRestriction.domainι Y (e t))
  simpa only [types_comp_apply, enriched_restrict_apply, enriched_comp_apply] using
    ConcreteCategory.congr_hom (enrichedRestriction.domainInverse_ι f e) t

theorem enrichedDomainFamilyEquiv_inverse {T : Type} {X Y : Numerical}
    (f : T ⟶ enrichedHom.hom X Y) (e : T ⟶ enrichedRestriction.domainObject Y) :
    enrichedDomainFamilyEquiv T X (enrichedRestriction.domainInverse f e) =
      fun t ↦ domainInverse (f t) (enrichedDomainFamilyEquiv T Y e t) := by
  funext t
  exact enrichedDomainInverse_apply f e t

/-- Pointwise numerical domain operations give the required internal domain lattices. -/
instance enrichedDomainLattices : enrichedRestriction.DomainLattices where
  lattice X T := typeHomDistribLattice T (enrichedRestriction.domainObject X)
  bounds X T := typeHomBoundedOrder T (enrichedRestriction.domainObject X)
  precomp {T T' X} k := (typeLattice (enrichedRestriction.domainObject X)).precomp k
  precomp_apply _ _ := rfl
  inf_ι {T X} a b := by
    apply ConcreteCategory.hom_ext
    intro t
    change (enrichedDomainEquiv X (a t ⊓ b t)).hom =
      enrichedHom.comp (a ≫ enrichedRestriction.domainι X)
        (b ≫ enrichedRestriction.domainι X) t
    rw [enriched_comp_apply]
    exact (congrArg Domain.hom ((enrichedDomainOrderIso X).map_inf (a t) (b t))).trans
      (Domain.inf_hom _ _)
  top_ι T X := by
    apply ConcreteCategory.hom_ext
    intro t
    change (enrichedDomainEquiv X ⊤).hom = (𝟙 X : X ⟶ X)
    exact (congrArg Domain.hom (enrichedDomainOrderIso X).map_top).trans (Domain.top_hom X)
  bot_ι T X := by
    apply ConcreteCategory.hom_ext
    intro t
    change (enrichedDomainEquiv X ⊥).hom = (0 : X ⟶ X)
    exact (congrArg Domain.hom (enrichedDomainOrderIso X).map_bot).trans (Domain.bot_hom X)
  pull_sup {T X Y} f a b := by
    apply (enrichedDomainFamilyEquiv T X).injective
    simp only [enrichedDomainFamilyEquiv_inverse, enrichedDomainFamilyEquiv_sup]
    funext t
    exact domainInverse_sup (f t) (enrichedDomainFamilyEquiv T Y a t)
      (enrichedDomainFamilyEquiv T Y b t)

end Numerical
end CategoricalEssentialIncompleteness
