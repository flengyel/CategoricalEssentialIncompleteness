/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.GlobalTotals

/-!
# Global restriction domains

Global points of the domain equalizers are identified with restriction
idempotents in the ordinary category. The transported lattice has the
restriction-domain order, composition as meet, and identity and zero as bounds.
The comparison commutes with the restriction inverse image.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace EnrichedRestriction
variable {V : Type u} [Category.{v} V] [HasFiniteLimits V] {O : Type w}
variable {H : InternalHom V O} (R : EnrichedRestriction H)

/-- A restriction idempotent of the underlying ordinary category. -/
@[ext] structure GlobalDomain (X : O) where
  hom : R.globalObject X ⟶ R.globalObject X
  isDomain : RestrictionCategory.rst hom = hom

/-- The fixed-point equalizer comparison, expressed in ordinary categorical terms. -/
def globalDomainEquiv (X : O) : (⊤_ V ⟶ R.domainObject X) ≃ R.GlobalDomain X :=
  (R.domainPointsEquiv (⊤_ V) X).trans
    { toFun := fun e ↦ ⟨e.val, e.property⟩
      invFun := fun e ↦ ⟨e.hom, e.isDomain⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

@[simp] theorem globalDomainEquiv_hom {X : O} (e : ⊤_ V ⟶ R.domainObject X) :
    (R.globalDomainEquiv X e).hom = (e ≫ R.domainι X : ⊤_ V ⟶ H.hom X X) := rfl

@[simp] theorem globalDomainEquiv_symm_ι {X : O} (e : R.GlobalDomain X) :
    (R.globalDomainEquiv X).symm e ≫ R.domainι X = e.hom :=
  R.domainLift_ι e.hom e.isDomain

theorem globalDomain_idem {X : O} (e : R.GlobalDomain X) : e.hom ≫ e.hom = e.hom := by
  have h := RestrictionCategory.rst_comp_self e.hom
  rwa [e.isDomain] at h

/-- Ordinary inverse image, defined by restriction of composition. -/
def globalDomainInverse {X Y : O} (f : R.globalObject X ⟶ R.globalObject Y)
    (e : R.GlobalDomain Y) : R.GlobalDomain X :=
  ⟨RestrictionCategory.rst (f ≫ e.hom), R.restrict_restrict (H.comp f e.hom)⟩

/-- The equalizer comparison is natural for restriction inverse image, even for partial arrows. -/
theorem globalDomainInverse_comparison {X Y : O}
    (f : R.globalObject X ⟶ R.globalObject Y) (e : ⊤_ V ⟶ R.domainObject Y) :
    R.globalDomainEquiv X (R.domainInverse f e) =
      R.globalDomainInverse f (R.globalDomainEquiv Y e) := by
  apply GlobalDomain.ext
  exact R.domainInverse_ι f e

theorem globalDomainInverse_point {X Y : O}
    (f : R.globalObject X ⟶ R.globalObject Y) (e : R.GlobalDomain Y) :
    (R.globalDomainEquiv X).symm (R.globalDomainInverse f e) =
      R.domainInverse f ((R.globalDomainEquiv Y).symm e) := by
  apply (R.globalDomainEquiv X).injective
  rw [Equiv.apply_symm_apply, R.globalDomainInverse_comparison, Equiv.apply_symm_apply]

variable [R.Zeros] [R.DomainLattices]

instance globalDomainLattice (X : O) : DistribLattice (R.GlobalDomain X) :=
  (R.globalDomainEquiv X).symm.distribLattice

instance globalDomainBounds (X : O) : BoundedOrder (R.GlobalDomain X) where
  top := R.globalDomainEquiv X ⊤
  bot := R.globalDomainEquiv X ⊥
  le_top a := by
    change (R.globalDomainEquiv X).symm a ≤ (R.globalDomainEquiv X).symm (R.globalDomainEquiv X ⊤)
    rw [Equiv.symm_apply_apply]
    exact le_top
  bot_le a := by
    change (R.globalDomainEquiv X).symm (R.globalDomainEquiv X ⊥) ≤ (R.globalDomainEquiv X).symm a
    rw [Equiv.symm_apply_apply]
    exact bot_le

/-- The finite-limit comparison is an isomorphism of bounded distributive lattices. -/
def globalDomainOrderIso (X : O) : (⊤_ V ⟶ R.domainObject X) ≃o R.GlobalDomain X where
  toEquiv := R.globalDomainEquiv X
  map_rel_iff' := by
    intro a b
    change (R.globalDomainEquiv X).symm (R.globalDomainEquiv X a) ≤
      (R.globalDomainEquiv X).symm (R.globalDomainEquiv X b) ↔ a ≤ b
    simp only [Equiv.symm_apply_apply]

theorem globalDomain_le_iff {X : O} (a b : R.GlobalDomain X) :
    a ≤ b ↔ a.hom ≫ b.hom = a.hom := by
  change (R.globalDomainEquiv X).symm a ≤ (R.globalDomainEquiv X).symm b ↔ _
  rw [R.domain_le_iff, R.globalDomainEquiv_symm_ι, R.globalDomainEquiv_symm_ι]
  rfl

@[simp] theorem globalDomain_inf_hom {X : O} (a b : R.GlobalDomain X) :
    (a ⊓ b).hom = a.hom ≫ b.hom := by
  rw [← R.globalDomainEquiv_symm_ι (a ⊓ b)]
  change (R.globalDomainOrderIso X).symm (a ⊓ b) ≫ R.domainι X = _
  rw [map_inf, DomainLattices.inf_ι]
  change H.comp ((R.globalDomainEquiv X).symm a ≫ R.domainι X)
    ((R.globalDomainEquiv X).symm b ≫ R.domainι X) = _
  rw [R.globalDomainEquiv_symm_ι, R.globalDomainEquiv_symm_ι]
  rfl

@[simp] theorem globalDomain_top_hom (X : O) :
    (⊤ : R.GlobalDomain X).hom = 𝟙 (R.globalObject X) := DomainLattices.top_ι _ _

@[simp] theorem globalDomain_bot_hom (X : O) :
    (⊥ : R.GlobalDomain X).hom = 0 := DomainLattices.bot_ι _ _

end EnrichedRestriction
end CategoricalEssentialIncompleteness
