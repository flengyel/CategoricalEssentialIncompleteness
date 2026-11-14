/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConstantFamilyProducts
public import CategoricalEssentialIncompleteness.V46RestrictionProductCategory

/-! # Turing morphisms for the products of the ambient partial slice -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.AmbientProductTuring

open AmbientPartialSlice AmbientSliceTuring RestrictionProducts
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable [Splits C] [HasPullbacks (RestrictionSubobjects.Tot C)] (T : C)

def fixedProduct (X : Family T) (Q : C) : BinaryProduct X (constantFamily T Q) where
  obj := tensorConstant X Q
  fst := tensorFst X Q
  snd := tensorSnd X Q
  pair := tensorPair
  fst_total := tensorFst_total _ _
  snd_total := tensorSnd_total _ _
  pair_fst := tensorPair_fst
  pair_snd := tensorPair_snd
  pair_restriction := tensorPair_restriction
  pair_proj := tensorPair_proj

def productIso (X : Family T) (Q : C) :
    AmbientSliceProducts.product X (constantFamily T Q) ≅ tensorConstant X Q :=
  ((AmbientSliceProducts.restrictionProducts T).binary X (constantFamily T Q)).iso
    (fixedProduct T X Q)

theorem comparison_naturality {X Y : Family T} (f : X ⟶ Y) (Q : C) (hf : isTotal f) :
    (AmbientSliceProducts.restrictionProducts T).map f (𝟙 (constantFamily T Q)) ≫
        (productIso T Y Q).hom = (productIso T X Q).hom ≫ tensorMap f Q := by
  let D := AmbientSliceProducts.restrictionProducts T
  have h0 (Z : Family T) : (productIso T Z Q).hom ≫ tensorFst Z Q = D.fst Z _ :=
    BinaryProduct.comparison_fst (D.binary Z _) (fixedProduct T Z Q)
  have h1 (Z : Family T) : (productIso T Z Q).hom ≫ tensorSnd Z Q = D.snd Z _ :=
    BinaryProduct.comparison_snd (D.binary Z _) (fixedProduct T Z Q)
  have hm0 : tensorMap f Q ≫ tensorFst Y Q = tensorFst X Q ≫ f := by
    rw [tensorMap_eq_pair, tensorPair_fst, tensorSnd_total, Category.id_comp]
  have hm1 : tensorMap f Q ≫ tensorSnd Y Q = tensorSnd X Q := by
    rw [tensorMap_eq_pair, tensorPair_snd,
      show rst (tensorFst X Q ≫ f) = 𝟙 _ from isTotal_comp (tensorFst_total _ _) hf,
      Category.id_comp]
  apply (fixedProduct T Y Q).hom_ext
  · change _ ≫ tensorFst Y Q = _ ≫ tensorFst Y Q
    rw [Category.assoc, h0, Category.assoc, hm0, ← Category.assoc, h0]
    exact D.map_fst_of_total f (𝟙 _) (rst_id _)
  · change _ ≫ tensorSnd Y Q = _ ≫ tensorSnd Y Q
    rw [Category.assoc, h1, Category.assoc, hm1, h1]
    exact (D.map_snd_of_total f (𝟙 _) hf).trans (Category.comp_id _)

def evaluator {Q : C} (τ : nearProd Q Q ⟶ Q) :
    AmbientSliceProducts.product (constantFamily T Q) (constantFamily T Q) ⟶ constantFamily T Q :=
  (productIso T (constantFamily T Q) Q).hom ≫ AmbientSliceTuring.evaluator T τ

theorem evaluator_isTuring {Q : C} (τ : nearProd Q Q ⟶ Q)
    (hτ : RecursionCategory.IsTuringMorphism τ) :
    @RecursionCategory.IsTuringMorphism (Family T) inferInstance
      (AmbientSliceProducts.restrictionProducts T).pcategoryStruct
      (AmbientSliceProducts.restrictionProducts T).pcategoryLaws
      (constantFamily T Q) (constantFamily T Q) (constantFamily T Q) (evaluator T τ) := by
  intro X φ
  change AmbientSliceProducts.product X (constantFamily T Q) ⟶ constantFamily T Q at φ
  obtain ⟨a, ha, hcode⟩ := parameterization τ hτ X ((productIso T X Q).inv ≫ φ)
  change tensorMap a Q ≫ AmbientSliceTuring.evaluator T τ = (productIso T X Q).inv ≫ φ at hcode
  refine ⟨a, ?_, ?_⟩
  · change @PCategoryStruct.rst (Family T) inferInstance
      (AmbientSliceProducts.restrictionProducts T).pcategoryStruct _ _ a = 𝟙 X
    rw [(AmbientSliceProducts.restrictionProducts T).restriction_eq]
    exact ha
  · change (AmbientSliceProducts.restrictionProducts T).map a (𝟙 _) ≫
      ((productIso T (constantFamily T Q) Q).hom ≫ AmbientSliceTuring.evaluator T τ) = φ
    rw [← Category.assoc, comparison_naturality T a Q ha, Category.assoc,
      hcode, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end CategoricalEssentialIncompleteness.V46.AmbientProductTuring
