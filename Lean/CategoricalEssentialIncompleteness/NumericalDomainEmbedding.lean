/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalSupportLattice
public import CategoricalEssentialIncompleteness.NumericalDomainReindexing

/-!
# The natural numerical domain embedding

The support inclusion of a restriction idempotent defines a PER subobject.
The embedding preserves the bounded lattice operations and commutes with
inverse image along total numerical arrows.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace NumericalPER

theorem supportSubobject_pullback {X Y A : Set ℕ}
    (f : Representative (discrete X) (discrete Y)) (hA : A ⊆ Y) :
    (Subobject.pullback (ofRepresentative f)).obj (supportSubobject A hA) =
      supportSubobject (inverseSupport f A) (fun _ h ↦ h.1) :=
  Subobject.pullback_obj_mk (i := inclusion hA)
    (j := inclusion (show inverseSupport f A ⊆ X from fun _ h ↦ h.1))
    (inverse_isPullback f hA).flip

end NumericalPER
namespace Numerical

theorem domainSubobject_naturality {X Y : Total} (f : X ⟶ Y) (e : Domain Y.obj) :
    (Subobject.pullback (toPER.map f)).obj (domainSubobject Y.obj e) =
      domainSubobject X.obj (domainInverse f.hom e) := by
  change (Subobject.pullback (NumericalPER.ofRepresentative (totalRepresentative f))).obj
    (NumericalPER.supportSubobject e.support _) =
      NumericalPER.supportSubobject (domainInverse f.hom e).support _
  rw [NumericalPER.supportSubobject_pullback]
  apply (NumericalPER.supportSubobject_eq_iff _ _).mpr
  exact (domainInverse_support_comparison f e).symm

@[simp] theorem domainSubobject_top (X : Numerical) :
    domainSubobject X ⊤ = ⊤ := by
  change NumericalPER.supportSubobject (⊤ : Domain X).support _ = ⊤
  rw [← NumericalPER.supportSubobject_top X.carrier]
  exact (NumericalPER.supportSubobject_eq_iff _ _).mpr (Domain.support_top X)

@[simp] theorem domainSubobject_bot (X : Numerical) :
    domainSubobject X ⊥ = ⊥ := by
  change NumericalPER.supportSubobject (⊥ : Domain X).support _ = ⊥
  rw [← NumericalPER.supportSubobject_bot X.carrier]
  exact (NumericalPER.supportSubobject_eq_iff _ _).mpr (Domain.support_bot X)

@[simp] theorem domainSubobject_inf {X : Numerical} (a b : Domain X) :
    domainSubobject X (a ⊓ b) = domainSubobject X a ⊓ domainSubobject X b := by
  change NumericalPER.supportSubobject (a ⊓ b).support _ =
    NumericalPER.supportSubobject a.support _ ⊓ NumericalPER.supportSubobject b.support _
  rw [← NumericalPER.supportSubobject_inf]
  exact (NumericalPER.supportSubobject_eq_iff _ _).mpr (Domain.support_inf a b)

@[simp] theorem domainSubobject_sup {X : Numerical} (a b : Domain X) :
    domainSubobject X (a ⊔ b) = domainSubobject X a ⊔ domainSubobject X b := by
  change NumericalPER.supportSubobject (a ⊔ b).support _ =
    NumericalPER.supportSubobject a.support _ ⊔ NumericalPER.supportSubobject b.support _
  rw [← NumericalPER.supportSubobject_sup a.support_enumerable b.support_enumerable]
  exact (NumericalPER.supportSubobject_eq_iff _ _).mpr (Domain.support_sup a b)

/-- The numerical restriction-domain embedding as a bounded lattice homomorphism. -/
def domainSubobjectHom (X : Numerical) :
    BoundedLatticeHom (Domain X) (Subobject (NumericalPER.discrete X.carrier)) where
  toFun := domainSubobject X
  map_sup' := domainSubobject_sup
  map_inf' := domainSubobject_inf
  map_top' := domainSubobject_top X
  map_bot' := domainSubobject_bot X

theorem domainSubobjectHom_injective (X : Numerical) :
    Function.Injective (domainSubobjectHom X) := (domainSubobject X).injective

/-- Complementarity of a specified pair is preserved and reflected by the embedding. -/
theorem domainSubobject_isCompl_iff {X : Numerical} (a b : Domain X) :
    IsCompl (domainSubobject X a) (domainSubobject X b) ↔ IsCompl a b := by
  constructor
  · intro h
    apply IsCompl.of_eq
    · apply (domainSubobject X).injective
      simpa only [domainSubobject_inf, domainSubobject_bot] using h.inf_eq_bot
    · apply (domainSubobject X).injective
      simpa only [domainSubobject_sup, domainSubobject_top] using h.sup_eq_top
  · intro h
    apply IsCompl.of_eq
    · rw [← domainSubobject_inf, h.inf_eq_bot, domainSubobject_bot]
    · rw [← domainSubobject_sup, h.sup_eq_top, domainSubobject_top]

end Numerical
end CategoricalEssentialIncompleteness
