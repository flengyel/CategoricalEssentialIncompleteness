/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalEnriched
public import CategoricalEssentialIncompleteness.NumericalTotalProducts
public import CategoricalEssentialIncompleteness.NumericalRecursion

/-!
# Numerical total hom-objects and internal indexing

The totality pullback in `Type` represents the set of total numerical morphisms. Its
operations agree with numerical identities, composition, and pairing. The numerical
parameter assignment lifts to this pullback and is a section of evaluation by the
Turing morphism.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace Numerical

/-- The numerical identity and zero are distinct as global enriched morphisms. -/
theorem enriched_nat_nontrivial :
    enrichedHom.unit nat ≠ EnrichedRestriction.Zeros.zero enrichedRestriction nat nat := by
  intro h
  exact nat_nontrivial (ConcreteCategory.congr_hom h default)

/-- A point of the totality pullback determines a total numerical morphism. -/
def enrichedTotalArrow {X Y : Numerical} (a : enrichedRestriction.totalObject X Y) :
    totalObject X ⟶ totalObject Y where
  hom := enrichedRestriction.totalι X Y a
  property := by
    change restrict (enrichedRestriction.totalι X Y a) = 𝟙 X
    have h := ConcreteCategory.congr_hom
      (enrichedRestriction.total_condition (𝟙 (enrichedRestriction.totalObject X Y))) a
    simpa only [enriched_restrict_apply, types_comp_apply, types_id_apply,
      enriched_identity_apply] using h

/-- The inclusion of total numerical morphisms lifts to the totality pullback. -/
def enrichedTotalLift (X Y : Numerical) :
    (totalObject X ⟶ totalObject Y) ⟶ enrichedRestriction.totalObject X Y :=
  enrichedRestriction.totalLift (TypeCat.ofHom fun f => f.hom) (by
    apply ConcreteCategory.hom_ext
    intro f
    change restrict f.hom = 𝟙 X
    exact f.property)

@[simp] theorem enrichedTotalLift_ι (X Y : Numerical)
    (f : totalObject X ⟶ totalObject Y) :
    enrichedRestriction.totalι X Y (enrichedTotalLift X Y f) = f.hom := by
  exact ConcreteCategory.congr_hom (enrichedRestriction.totalLift_ι _ _) f

/-- The totality pullback is equivalent to the numerical total hom-set. -/
def enrichedTotalEquiv (X Y : Numerical) :
    enrichedRestriction.totalObject X Y ≃ (totalObject X ⟶ totalObject Y) where
  toFun := enrichedTotalArrow
  invFun := enrichedTotalLift X Y
  left_inv a := by
    apply (CategoryTheory.injective_of_mono (enrichedRestriction.totalι X Y))
    exact enrichedTotalLift_ι X Y (enrichedTotalArrow a)
  right_inv f := by
    apply WideSubcategory.hom_ext
    exact enrichedTotalLift_ι X Y f

@[simp] theorem enrichedTotalEquiv_hom {X Y : Numerical}
    (a : enrichedRestriction.totalObject X Y) :
    (enrichedTotalEquiv X Y a).hom = enrichedRestriction.totalι X Y a := rfl

@[simp] theorem enrichedTotalEquiv_symm_ι {X Y : Numerical}
    (f : totalObject X ⟶ totalObject Y) :
    enrichedRestriction.totalι X Y ((enrichedTotalEquiv X Y).symm f) = f.hom :=
  enrichedTotalLift_ι X Y f

/-- The total hom-object identity corresponds to the numerical identity. -/
theorem enrichedTotal_identity {T : Type} (X : Numerical) (t : T) :
    enrichedTotalEquiv X X ((enrichedRestriction.totalHom enrichedProducts).identity X t) =
      𝟙 (totalObject X) := by
  apply WideSubcategory.hom_ext
  have h := ConcreteCategory.congr_hom
    (enrichedRestriction.total_identity_ι enrichedProducts (T := T) X) t
  change enrichedRestriction.totalι X X
    ((enrichedRestriction.totalHom enrichedProducts).identity X t) = 𝟙 X
  simp only [types_comp_apply, enriched_identity_apply] at h
  exact h

/-- Internal total composition agrees pointwise with numerical composition. -/
theorem enrichedTotal_comp {T : Type} {X Y Z : Numerical}
    (f : T ⟶ enrichedRestriction.totalObject X Y)
    (g : T ⟶ enrichedRestriction.totalObject Y Z) (t : T) :
    enrichedTotalEquiv X Z ((enrichedRestriction.totalHom enrichedProducts).comp f g t) =
      enrichedTotalEquiv X Y (f t) ≫ enrichedTotalEquiv Y Z (g t) := by
  apply WideSubcategory.hom_ext
  have h := ConcreteCategory.congr_hom
    (enrichedRestriction.total_comp_ι enrichedProducts f g) t
  change enrichedRestriction.totalι X Z
    ((enrichedRestriction.totalHom enrichedProducts).comp f g t) =
      enrichedRestriction.totalι X Y (f t) ≫ enrichedRestriction.totalι Y Z (g t)
  simp only [types_comp_apply, enriched_comp_apply] at h
  exact h

/-- Internal total pairing agrees pointwise with numerical pairing. -/
theorem enrichedTotal_pair {T : Type} {X Y Z : Numerical}
    (f : T ⟶ enrichedRestriction.totalObject X Y)
    (g : T ⟶ enrichedRestriction.totalObject X Z) (t : T) :
    enrichedTotalEquiv X (product Y Z)
        ((enrichedRestriction.totalHom enrichedProducts).pair f g t) =
      totalPair (enrichedTotalEquiv X Y (f t)) (enrichedTotalEquiv X Z (g t)) := by
  apply WideSubcategory.hom_ext
  have h := ConcreteCategory.congr_hom
    (enrichedRestriction.total_pair_ι enrichedProducts f g) t
  change enrichedRestriction.totalι X (product Y Z)
    ((enrichedRestriction.totalHom enrichedProducts).pair f g t) =
      partialPair (enrichedRestriction.totalι X Y (f t)) (enrichedRestriction.totalι X Z (g t))
  simp only [types_comp_apply, enriched_pair_apply] at h
  exact h

/-- The numerical indexing function lifted to an internal total hom-object. -/
def internalIndexing (V : Numerical) :
    enrichedHom.hom (product V nat) nat ⟶ enrichedRestriction.totalObject V nat :=
  TypeCat.ofHom (fun φ => turingIndexing V φ) ≫ enrichedTotalLift V nat

@[simp] theorem internalIndexing_ι (V : Numerical) (φ : product V nat ⟶ nat) :
    enrichedRestriction.totalι V nat (internalIndexing V φ) = (turingIndexing V φ).hom := by
  exact enrichedTotalLift_ι V nat _

/-- Evaluation of a total parameter morphism by the numerical Turing morphism. -/
def internalEvaluation (V : Numerical) :
    enrichedRestriction.totalObject V nat ⟶ enrichedHom.hom (product V nat) nat :=
  TypeCat.ofHom fun g =>
    partialProdMap (enrichedRestriction.totalι V nat g) (𝟙 nat) ≫ turingEvaluator

/-- Internal evaluation is composition with the Turing morphism after the product of the
total parameter morphism and the identity. -/
theorem internalEvaluation_composition {T : Type} (V : Numerical)
    (g : T ⟶ enrichedRestriction.totalObject V nat) :
    g ≫ internalEvaluation V =
      enrichedHom.comp
        (enrichedHom.pair
          (enrichedHom.comp (enrichedHom.fst V nat) (g ≫ enrichedRestriction.totalι V nat))
          (enrichedHom.snd V nat))
        (TypeCat.ofHom fun _ : T => turingEvaluator) := by
  apply ConcreteCategory.hom_ext
  intro t
  change partialProdMap (enrichedRestriction.totalι V nat (g t)) (𝟙 nat) ≫ turingEvaluator =
    enrichedHom.comp
      (enrichedHom.pair
        (enrichedHom.comp (enrichedHom.fst V nat) (g ≫ enrichedRestriction.totalι V nat))
        (enrichedHom.snd V nat)) (TypeCat.ofHom fun _ : T => turingEvaluator) t
  rw [enriched_comp_apply, enriched_pair_apply, enriched_comp_apply,
    enriched_fst_apply, enriched_snd_apply]
  simp only [partialProdMap, types_comp_apply, TypeCat.ofHom_apply, Category.comp_id]

/-- Internal indexing is a section of evaluation. -/
theorem internalIndexing_evaluation (V : Numerical) :
    internalIndexing V ≫ internalEvaluation V = 𝟙 _ := by
  apply ConcreteCategory.hom_ext
  intro φ
  change partialProdMap (enrichedRestriction.totalι V nat (internalIndexing V φ))
    (𝟙 nat) ≫ turingEvaluator = φ
  rw [internalIndexing_ι]
  exact turingIndexing_evaluation V φ

end Numerical
end CategoricalEssentialIncompleteness
