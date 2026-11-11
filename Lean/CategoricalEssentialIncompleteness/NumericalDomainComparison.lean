/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalPCategory
public import CategoricalEssentialIncompleteness.NumericalDomainReindexing
public import CategoricalEssentialIncompleteness.RestrictionPredicates

/-!
# Numerical domains and the P-category domain lattice

The original numerical restriction domains are order isomorphic to the
domains of the numerical P-category, with the same underlying arrows.
The comparison transports the numerical joins and their inverse-image laws
to the P-category domain lattice.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory
namespace CategoricalEssentialIncompleteness
namespace Numerical

/-- The two domain presentations have identical arrows and the same restriction order. -/
def domainOrderIso (X : Numerical) : Domain X ≃o DomSemilattice X where
  toFun e := ⟨e.hom, (pcategory_rst_eq e.hom).trans e.isDomain⟩
  invFun e := ⟨e.hom, (pcategory_rst_eq e.hom).symm.trans e.isDomain⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := (Domain.le_iff _ _).symm

@[simp] theorem domainOrderIso_hom {X : Numerical} (e : Domain X) :
    (domainOrderIso X e).hom = e.hom := rfl

@[simp] theorem domainOrderIso_symm_hom {X : Numerical} (e : DomSemilattice X) :
    ((domainOrderIso X).symm e).hom = e.hom := rfl

/-- Composition as a domain meet agrees with the numerical lattice meet. -/
theorem domainOrderIso_symm_meet {X : Numerical} (a b : DomSemilattice X) :
    (domainOrderIso X).symm (DomSemilattice.meet a b) =
      (domainOrderIso X).symm a ⊓ (domainOrderIso X).symm b := by
  apply Domain.ext
  exact (Domain.inf_hom ((domainOrderIso X).symm a) ((domainOrderIso X).symm b)).symm

/-- The domain comparison commutes with restriction inverse image along partial arrows. -/
theorem domainOrderIso_inverse {X Y : Numerical} (f : X ⟶ Y) (e : Domain Y) :
    domainOrderIso X (domainInverse f e) = domainInverseImage f (domainOrderIso Y e) := by
  apply DomSemilattice.ext'
  exact (pcategory_rst_eq (f ≫ e.hom)).symm

theorem domainOrderIso_symm_inverse {X Y : Numerical} (f : X ⟶ Y)
    (e : DomSemilattice Y) :
    (domainOrderIso X).symm (domainInverseImage f e) =
      domainInverse f ((domainOrderIso Y).symm e) := by
  apply Domain.ext
  exact pcategory_rst_eq (f ≫ e.hom)

/-- C.e. unions supply the P-category joins and their inverse-image stability. -/
instance numericalDomainJoins : DomainJoins Numerical where
  join {X} a b := domainOrderIso X ((domainOrderIso X).symm a ⊔ (domainOrderIso X).symm b)
  le_join_left {X} a b := by
    simpa only [OrderIso.apply_symm_apply] using
      (domainOrderIso X).monotone
        (le_sup_left : (domainOrderIso X).symm a ≤
          (domainOrderIso X).symm a ⊔ (domainOrderIso X).symm b)
  le_join_right {X} a b := by
    simpa only [OrderIso.apply_symm_apply] using
      (domainOrderIso X).monotone
        (le_sup_right : (domainOrderIso X).symm b ≤
          (domainOrderIso X).symm a ⊔ (domainOrderIso X).symm b)
  join_le {X} a b c ha hb := by
    simpa only [OrderIso.apply_symm_apply] using
      (domainOrderIso X).monotone
        (sup_le ((domainOrderIso X).symm.monotone ha) ((domainOrderIso X).symm.monotone hb))
  distrib {X} a b c := by
    apply (domainOrderIso X).symm.le_iff_le.mp
    simp only [domainOrderIso_symm_meet, OrderIso.symm_apply_apply]
    exact le_sup_inf
  pull_join {X Y} f _ a b := by
    apply (domainOrderIso X).symm.injective
    simp only [domainOrderIso_symm_inverse, OrderIso.symm_apply_apply]
    exact domainInverse_sup f ((domainOrderIso Y).symm a) ((domainOrderIso Y).symm b)

/-- The domain comparison preserves bounds and both lattice operations. -/
def domainComparisonHom (X : Numerical) : BoundedLatticeHom (Domain X) (DomSemilattice X) where
  toFun := domainOrderIso X
  map_sup' := (domainOrderIso X).map_sup
  map_inf' := (domainOrderIso X).map_inf
  map_top' := (domainOrderIso X).map_top
  map_bot' := (domainOrderIso X).map_bot

theorem domainComparisonHom_bijective (X : Numerical) :
    Function.Bijective (domainComparisonHom X) := (domainOrderIso X).bijective

/-- The bounded lattice comparison retains the partial inverse-image equation. -/
theorem domainComparisonHom_inverse {X Y : Numerical} (f : X ⟶ Y) (e : Domain Y) :
    domainComparisonHom X (domainInverse f e) =
      domainInverseImage f (domainComparisonHom Y e) := domainOrderIso_inverse f e

end Numerical
end CategoricalEssentialIncompleteness
