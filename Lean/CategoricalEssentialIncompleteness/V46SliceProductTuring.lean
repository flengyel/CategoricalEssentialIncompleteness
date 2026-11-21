/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSliceProducts
public import CategoricalEssentialIncompleteness.V46RestrictionProductComparison

/-! # Turing morphisms for the binary products of the partial-map slice -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.SliceProductTuring

open RestrictionSubobjects PartialSliceTuring RestrictionProducts

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [HasPullbacks (Tot C)]
variable (inverses : MonoInverses C) (T : Tot C)

def fixedProduct (X : PartialMaps.Par (Over T)) (Q : C) :
    BinaryProduct X (constantObject T Q) where
  obj := (tensorFunctor inverses T Q).obj X
  fst := tensorFst inverses T Q X
  snd := tensorSnd inverses T Q X
  pair := tensorPair inverses T
  fst_total := tensorFst_total inverses T Q X
  snd_total := tensorSnd_total inverses T Q X
  pair_fst := tensorPair_fst inverses T
  pair_snd := tensorPair_snd inverses T
  pair_restriction := tensorPair_restriction inverses T
  pair_proj := tensorPair_proj inverses T

def productIso (X : PartialMaps.Par (Over T)) (Q : C) :
    PartialSliceProducts.product inverses T X (constantObject T Q) ≅
      (tensorFunctor inverses T Q).obj X :=
  ((PartialSliceProducts.restrictionProducts inverses T).binary X (constantObject T Q)).iso
    (fixedProduct inverses T X Q)

theorem productIso_fst (X : PartialMaps.Par (Over T)) (Q : C) :
    (productIso inverses T X Q).hom ≫ tensorFst inverses T Q X =
      PartialSliceProducts.first inverses T X (constantObject T Q) :=
  BinaryProduct.comparison_fst
    ((PartialSliceProducts.restrictionProducts inverses T).binary X (constantObject T Q))
    (fixedProduct inverses T X Q)

theorem productIso_snd (X : PartialMaps.Par (Over T)) (Q : C) :
    (productIso inverses T X Q).hom ≫ tensorSnd inverses T Q X =
      PartialSliceProducts.second inverses T X (constantObject T Q) :=
  BinaryProduct.comparison_snd
    ((PartialSliceProducts.restrictionProducts inverses T).binary X (constantObject T Q))
    (fixedProduct inverses T X Q)

theorem productIso_total (X : PartialMaps.Par (Over T)) (Q : C) :
    isTotal (productIso inverses T X Q).hom :=
  BinaryProduct.comparison_total
    ((PartialSliceProducts.restrictionProducts inverses T).binary X (constantObject T Q))
    (fixedProduct inverses T X Q)

theorem tensorMap_eq_pair {X Y : PartialMaps.Par (Over T)} (f : X ⟶ Y) (Q : C) :
    (tensorFunctor inverses T Q).map f =
      tensorPair inverses T (tensorFst inverses T Q X ≫ f) (tensorSnd inverses T Q X) := by
  apply (PartialSliceEquivalence.functor inverses T).map_injective
  change (PartialSliceEquivalence.functor inverses T).map ((realization inverses T).map
      ((AmbientSliceTuring.tensorFunctor T.obj Q).map
        ((PartialSliceEquivalence.functor inverses T).map f))) = _
  rw [map_realization, tensorPair_value, CategoryTheory.Functor.map_comp,
    tensorFst_value, tensorSnd_value]
  exact AmbientSliceTuring.tensorMap_eq_pair _ Q

theorem tensorMap_fst {X Y : PartialMaps.Par (Over T)} (f : X ⟶ Y) (Q : C) :
    (tensorFunctor inverses T Q).map f ≫ tensorFst inverses T Q Y =
      tensorFst inverses T Q X ≫ f := by
  rw [tensorMap_eq_pair, tensorPair_fst, tensorSnd_total, Category.id_comp]

theorem tensorMap_snd {X Y : PartialMaps.Par (Over T)} (f : X ⟶ Y) (Q : C)
    (hf : isTotal f) :
    (tensorFunctor inverses T Q).map f ≫ tensorSnd inverses T Q Y =
      tensorSnd inverses T Q X := by
  rw [tensorMap_eq_pair, tensorPair_snd, show rst (tensorFst inverses T Q X ≫ f) = 𝟙 _
    from isTotal_comp (tensorFst_total inverses T Q X) hf, Category.id_comp]

theorem productIso_naturality {X Y : PartialMaps.Par (Over T)} (f : X ⟶ Y) (Q : C)
    (hf : isTotal f) :
    (PartialSliceProducts.restrictionProducts inverses T).map f (𝟙 (constantObject T Q)) ≫
        (productIso inverses T Y Q).hom =
      (productIso inverses T X Q).hom ≫ (tensorFunctor inverses T Q).map f := by
  apply (fixedProduct inverses T Y Q).hom_ext
  · change _ ≫ tensorFst inverses T Q Y = _ ≫ tensorFst inverses T Q Y
    rw [Category.assoc, productIso_fst, Category.assoc, tensorMap_fst,
      ← Category.assoc, productIso_fst]
    exact (PartialSliceProducts.restrictionProducts inverses T).map_fst_of_total
      f (𝟙 (constantObject T Q)) (rst_id _)
  · change _ ≫ tensorSnd inverses T Q Y = _ ≫ tensorSnd inverses T Q Y
    rw [Category.assoc, productIso_snd, Category.assoc, tensorMap_snd inverses T f Q hf,
      productIso_snd]
    have h := (PartialSliceProducts.restrictionProducts inverses T).map_snd_of_total
      f (𝟙 (constantObject T Q)) hf
    change _ = PartialSliceProducts.second inverses T X (constantObject T Q) ≫ 𝟙 _ at h
    exact h.trans (Category.comp_id _)

def evaluator {Q : C} (τ : nearProd Q Q ⟶ Q) :
    PartialSliceProducts.product inverses T (constantObject T Q) (constantObject T Q) ⟶
      constantObject T Q :=
  (productIso inverses T (constantObject T Q) Q).hom ≫ PartialSliceTuring.evaluator inverses T τ

/-- The slice evaluator is a Turing morphism for its chosen binary products, with
parameters ranging over every object of the span quotient. -/
theorem evaluator_isTuring {Q : C} (τ : nearProd Q Q ⟶ Q)
    (hτ : RecursionCategory.IsTuringMorphism τ) :
    @RecursionCategory.IsTuringMorphism (PartialMaps.Par (Over T)) inferInstance
      (PartialSliceProducts.pcategoryStruct inverses T)
      (PartialSliceProducts.pcategoryLaws inverses T)
      (constantObject T Q) (constantObject T Q) (constantObject T Q)
      (evaluator inverses T τ) := by
  intro X φ
  obtain ⟨a, ha, hcode⟩ := parameterization inverses T τ hτ X
    ((productIso inverses T X Q).inv ≫ φ)
  refine ⟨a, ?_, ?_⟩
  · change @PCategoryStruct.rst _ _ (PartialSliceProducts.pcategoryStruct inverses T)
      X (constantObject T Q) a = 𝟙 X
    rw [(PartialSliceProducts.restrictionProducts inverses T).restriction_eq]
    exact ha
  · change (PartialSliceProducts.restrictionProducts inverses T).map a (𝟙 _) ≫
      ((productIso inverses T (constantObject T Q) Q).hom ≫
        PartialSliceTuring.evaluator inverses T τ) = φ
    rw [← Category.assoc, productIso_naturality inverses T a Q ha, Category.assoc,
      hcode, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end CategoricalEssentialIncompleteness.V46.SliceProductTuring
