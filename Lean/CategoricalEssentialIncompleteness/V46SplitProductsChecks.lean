/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SplitProducts

/-! # Restriction products with arbitrary split objects and partial morphisms -/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness SplitObject

variable {R : Type u} [Category.{v} R] [PCategoryStruct R] [PCategory R]

example {W X Y : SplitObject R} (f : W ⟶ X) (g : W ⟶ Y) :
    rst (binaryProductPair f g) = rst f ≫ rst g ∧
      binaryProductPair f g ≫ binaryProductFst X Y = rst g ≫ f ∧
      binaryProductPair f g ≫ binaryProductSnd X Y = rst f ≫ g :=
  ⟨binaryProductPair_restriction f g, binaryProductPair_fst f g,
    binaryProductPair_snd f g⟩

example {W X Y : SplitObject R} (f : W ⟶ X) (g : W ⟶ Y)
    (hf : isTotal f) (hg : isTotal g) :
    ∃! h : W ⟶ binaryProduct X Y,
      isTotal h ∧ h ≫ binaryProductFst X Y = f ∧ h ≫ binaryProductSnd X Y = g :=
  binaryProduct_existsUnique f g hf hg

example (X Y : SplitObject R) :
    isTotal (binaryProductFst X Y) ∧ isTotal (binaryProductSnd X Y) :=
  ⟨binaryProductFst_total X Y, binaryProductSnd_total X Y⟩

example {X Y : SplitObject R} (f : X ⟶ Y) :
    @PCategoryStruct.rst (SplitObject R) inferInstance productData X Y f = rst f :=
  productData_restriction f

#print axioms SplitObject.binaryProductPair_restriction
#print axioms SplitObject.binaryProductPair_fst
#print axioms SplitObject.binaryProductPair_snd
#print axioms SplitObject.binaryProductPair_proj
#print axioms SplitObject.binaryProduct_hom_ext
#print axioms SplitObject.binaryProduct_existsUnique
#print axioms SplitObject.binaryProductFst_total
#print axioms SplitObject.binaryProductSnd_total
#print axioms SplitObject.productData_partialPairing
#print axioms SplitObject.productData_restriction
