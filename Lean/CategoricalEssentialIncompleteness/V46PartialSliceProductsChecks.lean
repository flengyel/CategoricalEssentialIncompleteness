/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SplitSliceTuring

/-! # Statement and axiom checks for arbitrary slice products and Turing morphisms -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46 RestrictionSubobjects

section Restriction

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]

example (D : RestrictionProducts.ProductData C) : @PCategory C inferInstance D.pcategoryStruct :=
  D.pcategoryLaws

example (D : RestrictionProducts.ProductData C) :
    @PCategory.inducedRestriction C inferInstance D.pcategoryStruct D.pcategoryLaws =
      (inferInstance : RestrictionCategory C) := D.restrictionCategory_eq

example {X Y : C} (P Q : RestrictionProducts.BinaryProduct X Y) : P.obj ≅ Q.obj := P.iso Q

example [Splits C] {T : C} {X : AmbientPartialSlice.Family T} (a : Idem X) :
    ∃ (Z : AmbientPartialSlice.Family T) (m : Z ⟶ X) (r : X ⟶ Z),
      isTotal m ∧ m ≫ r = 𝟙 Z ∧ r ≫ m = a.hom :=
  PartialSliceSplitting.ambient_splitting a

example [Splits C] [HasPullbacks (Tot C)] (inverses : MonoInverses C) (T : Tot C) :
    Splits (PartialMaps.Par (Over T)) := PartialSliceSplitting.partialSliceSplits inverses T

example [Splits C] [HasPullbacks (Tot C)] {T : C} {V X Y : AmbientPartialSlice.Family T}
    (f : V ⟶ X) (g : V ⟶ Y) :
    rst (AmbientSliceProducts.pair f g) = rst f ≫ rst g ∧
      AmbientSliceProducts.pair f g ≫ AmbientSliceProducts.first X Y = rst g ≫ f ∧
      AmbientSliceProducts.pair f g ≫ AmbientSliceProducts.second X Y = rst f ≫ g :=
  ⟨AmbientSliceProducts.pair_restriction f g,
    AmbientSliceProducts.pair_fst f g, AmbientSliceProducts.pair_snd f g⟩

end Restriction

section Turing

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable [Splits C] [HasPullbacks (Tot C)]
variable (inverses : MonoInverses C) (T : Tot C)

example : @PCategory (PartialMaps.Par (Over T)) inferInstance
    (PartialSliceProducts.pcategoryStruct inverses T) :=
  PartialSliceProducts.pcategoryLaws inverses T

example : @PCategory.inducedRestriction (PartialMaps.Par (Over T)) inferInstance
    (PartialSliceProducts.pcategoryStruct inverses T)
      (PartialSliceProducts.pcategoryLaws inverses T) =
      (inferInstance : RestrictionCategory (PartialMaps.Par (Over T))) :=
  PartialSliceProducts.restrictionCategory_eq inverses T

example {V X Y : PartialMaps.Par (Over T)} (f : V ⟶ X) (g : V ⟶ Y) :
    rst (PartialSliceProducts.pair inverses T f g) = rst f ≫ rst g ∧
      PartialSliceProducts.pair inverses T f g ≫ PartialSliceProducts.first inverses T X Y =
        rst g ≫ f ∧
      PartialSliceProducts.pair inverses T f g ≫ PartialSliceProducts.second inverses T X Y =
        rst f ≫ g :=
  ⟨PartialSliceProducts.pair_restriction inverses T f g,
    PartialSliceProducts.pair_fst inverses T f g, PartialSliceProducts.pair_snd inverses T f g⟩

example {V X Y : PartialMaps.Par (Over T)}
    (h : V ⟶ PartialSliceProducts.product inverses T X Y) :
    PartialSliceProducts.pair inverses T (h ≫ PartialSliceProducts.first inverses T X Y)
      (h ≫ PartialSliceProducts.second inverses T X Y) = h :=
  PartialSliceProducts.pair_proj inverses T h

example (X : PartialMaps.Par (Over T)) (Q : C) :
    PartialSliceProducts.product inverses T X (PartialSliceTuring.constantObject T Q) ≅
      (PartialSliceTuring.tensorFunctor inverses T Q).obj X :=
  SliceProductTuring.productIso inverses T X Q

example {Q : C} (τ : nearProd Q Q ⟶ Q) (hτ : RecursionCategory.IsTuringMorphism τ) :
    @RecursionCategory.IsTuringMorphism (PartialMaps.Par (Over T)) inferInstance
      (PartialSliceProducts.pcategoryStruct inverses T)
      (PartialSliceProducts.pcategoryLaws inverses T)
      (PartialSliceTuring.constantObject T Q) (PartialSliceTuring.constantObject T Q)
      (PartialSliceTuring.constantObject T Q) (SliceProductTuring.evaluator inverses T τ) :=
  SliceProductTuring.evaluator_isTuring inverses T τ hτ

example {X Y : PartialMaps.Par (Over T)} (f : X ⟶ Y) :
    f ≫ PartialSliceRetractions.terminate inverses T Y =
      rst f ≫ PartialSliceRetractions.terminate inverses T X :=
  PartialSliceRetractions.terminate_naturality inverses T f

example {Q : C}
    (hQ : ∀ Y : C, ∃ (m : Y ⟶ Q) (r : Q ⟶ Y), isTotal m ∧ m ≫ r = 𝟙 Y)
    (X : PartialMaps.Par (Over T)) :
    ∃ (j : X ⟶ PartialSliceTuring.constantObject T Q)
      (s : PartialSliceTuring.constantObject T Q ⟶ X),
      isTotal j ∧ j ≫ s = 𝟙 X ∧ s ≫ j = rst s :=
  PartialSliceRetractions.exists_total_retract inverses T hQ X

end Turing

#check SplitSliceTuring.turing_object

#print axioms RestrictionProducts.ProductData.comp_pair
#print axioms RestrictionProducts.ProductData.pair_cross_masks
#print axioms RestrictionProducts.ProductData.map_comp
#print axioms RestrictionProducts.ProductData.associator_nat
#print axioms RestrictionProducts.ProductData.symmetry_nat
#print axioms RestrictionProducts.ProductData.pcategoryLaws
#print axioms RestrictionProducts.ProductData.restrictionCategory_eq
#print axioms RestrictionProducts.BinaryProduct.comparison_total
#print axioms RestrictionProducts.BinaryProduct.iso
#print axioms AmbientSliceProducts.partial_pullback_hom_ext
#print axioms AmbientSliceProducts.exists_pairing
#print axioms AmbientSliceProducts.pair_fst
#print axioms AmbientSliceProducts.pair_snd
#print axioms AmbientSliceProducts.pair_restriction
#print axioms AmbientSliceProducts.pair_proj
#print axioms PartialSliceProducts.first_total
#print axioms PartialSliceProducts.second_total
#print axioms PartialSliceProducts.pair_fst
#print axioms PartialSliceProducts.pair_snd
#print axioms PartialSliceProducts.pair_restriction
#print axioms PartialSliceProducts.pair_proj
#print axioms PartialSliceProducts.pcategoryLaws
#print axioms PartialSliceProducts.restrictionCategory_eq
#print axioms SliceProductTuring.productIso
#print axioms SliceProductTuring.productIso_naturality
#print axioms SliceProductTuring.evaluator_isTuring
#print axioms PartialSliceRetractions.terminate_total
#print axioms PartialSliceRetractions.terminate_self
#print axioms PartialSliceRetractions.terminate_naturality
#print axioms PartialSliceRetractions.terminate_unique
#print axioms PartialSliceRetractions.total_retract
#print axioms PartialSliceRetractions.exists_total_retract
#print axioms PartialSliceSplitting.ambient_splitting
#print axioms PartialSliceSplitting.splitting
#print axioms PartialSliceSplitting.partialSliceSplits
#print axioms SplitSliceTuring.turing_object
