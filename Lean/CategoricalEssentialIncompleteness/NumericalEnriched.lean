/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EnrichedDomains
public import CategoricalEssentialIncompleteness.NumericalPartialProducts
public import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Set-enrichment of the numerical restriction category

The hom-objects are the sets of extensional partial recursive morphisms. Composition,
restriction, and partial pairing act pointwise on families of morphisms. Their
equations give enriched restriction products and zeros over the category of types.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace Numerical

/-- Numerical hom-sets, with pointwise composition and partial pairing. -/
def enrichedHom : InternalHom (Type) Numerical where
  hom X Y := X ⟶ Y
  unit X := ↾fun _ ↦ 𝟙 X
  composition X Y Z := ↾fun p ↦
    (prod.fst : (X ⟶ Y) ⨯ (Y ⟶ Z) ⟶ (X ⟶ Y)) p ≫
      (prod.snd : (X ⟶ Y) ⨯ (Y ⟶ Z) ⟶ (Y ⟶ Z)) p
  product := product
  first X Y := ↾fun _ ↦ partialFst X Y
  second X Y := ↾fun _ ↦ partialSnd X Y
  pairing X Y Z := ↾fun p ↦
    partialPair ((prod.fst : (X ⟶ Y) ⨯ (X ⟶ Z) ⟶ (X ⟶ Y)) p)
      ((prod.snd : (X ⟶ Y) ⨯ (X ⟶ Z) ⟶ (X ⟶ Z)) p)

@[simp] theorem enriched_identity_apply {T : Type} (X : Numerical) (t : T) :
    enrichedHom.identity X t = 𝟙 X := rfl

@[simp] theorem enriched_comp_apply {T : Type} {X Y Z : Numerical}
    (f : T ⟶ enrichedHom.hom X Y) (g : T ⟶ enrichedHom.hom Y Z) (t : T) :
    enrichedHom.comp f g t = f t ≫ g t := by
  change (prod.lift f g ≫ prod.fst) t ≫ (prod.lift f g ≫ prod.snd) t = _
  rw [prod.lift_fst, prod.lift_snd]

@[simp] theorem enriched_pair_apply {T : Type} {X Y Z : Numerical}
    (f : T ⟶ enrichedHom.hom X Y) (g : T ⟶ enrichedHom.hom X Z) (t : T) :
    enrichedHom.pair f g t = partialPair (f t) (g t) := by
  change partialPair ((prod.lift f g ≫ prod.fst) t) ((prod.lift f g ≫ prod.snd) t) = _
  rw [prod.lift_fst, prod.lift_snd]

@[simp] theorem enriched_fst_apply {T : Type} (X Y : Numerical) (t : T) :
    enrichedHom.fst X Y t = partialFst X Y := rfl

@[simp] theorem enriched_snd_apply {T : Type} (X Y : Numerical) (t : T) :
    enrichedHom.snd X Y t = partialSnd X Y := rfl

/-- Restriction of each member of a family satisfies the enriched restriction equations. -/
def enrichedRestriction : EnrichedRestriction enrichedHom where
  restriction X Y := ↾fun f ↦ restrict f
  assoc f g h := by
    apply ConcreteCategory.hom_ext
    intro t
    simp only [enriched_comp_apply, Category.assoc]
  id_comp f := by
    apply ConcreteCategory.hom_ext
    intro t
    simp only [enriched_comp_apply, enriched_identity_apply, Category.id_comp]
  comp_id f := by
    apply ConcreteCategory.hom_ext
    intro t
    simp only [enriched_comp_apply, enriched_identity_apply, Category.comp_id]
  rst_comp_self f := by
    apply ConcreteCategory.hom_ext
    intro t
    simp only [enriched_comp_apply, types_comp_apply, TypeCat.ofHom_apply]
    exact @RestrictionCategory.rst_comp_self Numerical numericalCategory numericalRestriction
      _ _ (f t)
  rst_comm f g := by
    apply ConcreteCategory.hom_ext
    intro t
    simp only [enriched_comp_apply, types_comp_apply, TypeCat.ofHom_apply]
    exact @RestrictionCategory.rst_comm Numerical numericalCategory numericalRestriction
      _ _ _ (f t) (g t)
  rst_comp_rst f g := by
    apply ConcreteCategory.hom_ext
    intro t
    simp only [enriched_comp_apply, types_comp_apply, TypeCat.ofHom_apply]
    exact @RestrictionCategory.rst_comp_rst Numerical numericalCategory numericalRestriction _ _ _
      (f t) (g t)
  rst_comp f g := by
    apply ConcreteCategory.hom_ext
    intro t
    simp only [enriched_comp_apply, types_comp_apply, TypeCat.ofHom_apply]
    exact @RestrictionCategory.rst_comp Numerical numericalCategory numericalRestriction _ _ _
      (f t) (g t)

@[simp] theorem enriched_restriction_apply {X Y : Numerical} (f : X ⟶ Y) :
    enrichedRestriction.restriction X Y f = restrict f := rfl

@[simp] theorem enriched_restrict_apply {T : Type} {X Y : Numerical}
    (f : T ⟶ enrichedHom.hom X Y) (t : T) :
    enrichedRestriction.restrict f t = restrict (f t) := rfl

/-- Partial numerical products satisfy the enriched restriction-product equations. -/
theorem enrichedProducts : enrichedRestriction.Products where
  first_total X Y := by
    apply ConcreteCategory.hom_ext
    intro t
    exact partialFst_total X Y
  second_total X Y := by
    apply ConcreteCategory.hom_ext
    intro t
    exact partialSnd_total X Y
  pair_fst f g := by
    apply ConcreteCategory.hom_ext
    intro t
    simpa only [enriched_comp_apply, enriched_pair_apply, enriched_fst_apply,
      enriched_restrict_apply] using partialPair_fst (f t) (g t)
  pair_snd f g := by
    apply ConcreteCategory.hom_ext
    intro t
    simpa only [enriched_comp_apply, enriched_pair_apply, enriched_snd_apply,
      enriched_restrict_apply] using partialPair_snd (f t) (g t)
  pair_eta f := by
    apply ConcreteCategory.hom_ext
    intro t
    simpa only [enriched_pair_apply, enriched_comp_apply, enriched_fst_apply,
      enriched_snd_apply] using partialPair_proj (f t)

/-- The nowhere-defined numerical morphisms give enriched zero morphisms. -/
instance enrichedZeros : enrichedRestriction.Zeros where
  zero X Y := ↾fun _ ↦ (0 : X ⟶ Y)
  zero_comp f := by
    apply ConcreteCategory.hom_ext
    intro t
    simp only [enriched_comp_apply, types_comp_apply, TypeCat.ofHom_apply, Limits.zero_comp]
  comp_zero f := by
    apply ConcreteCategory.hom_ext
    intro t
    simp only [enriched_comp_apply, types_comp_apply, TypeCat.ofHom_apply, Limits.comp_zero]
  restriction_zero X Y := by
    apply ConcreteCategory.hom_ext
    intro t
    exact restrict_zero X Y

@[simp] theorem enriched_zero_apply {T : Type} (X Y : Numerical) (t : T) :
    enrichedRestriction.zeroAt T X Y t = (0 : X ⟶ Y) := rfl

end Numerical
end CategoricalEssentialIncompleteness
