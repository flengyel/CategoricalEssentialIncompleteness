/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46AmbientSliceProducts
public import CategoricalEssentialIncompleteness.V46AmbientSliceTuring
public import CategoricalEssentialIncompleteness.V46RestrictionProductComparison

/-! # Constant families and their binary product comparisons -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ConstantFamilyProducts

open AmbientPartialSlice AmbientSliceTuring RestrictionProducts
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

def constantFunctor (T : C) : C ⥤ Family T where
  obj := constantFamily T
  map := constantMap T
  map_id X := Hom.ext (PCategory.nearProd_id T X)
  map_comp f g := Hom.ext (by
    change nearProd_map (𝟙 T) (f ≫ g) = nearProd_map (𝟙 T) f ≫ nearProd_map (𝟙 T) g
    rw [PCategory.nearProd_comp, Category.id_comp])

def familyIso {T : C} (X Y : Family T) (i : X.base ≅ Y.base)
    (hi : i.hom ≫ Y.proj = X.proj) : X ≅ Y where
  hom := ⟨i.hom, by rw [iso_total i, Category.id_comp]; exact hi⟩
  inv := ⟨i.inv, by
    have ht : isTotal i.inv := iso_total i.symm
    rw [ht, Category.id_comp, ← hi, ← Category.assoc, i.inv_hom_id, Category.id_comp]⟩
  hom_inv_id := Hom.ext i.hom_inv_id
  inv_hom_id := Hom.ext i.inv_hom_id

def associatorIso (T X Y : C) :
    tensorConstant (constantFamily T X) Y ≅ constantFamily T (nearProd X Y) :=
  familyIso _ _
    ⟨assoc T X Y, PCategory.assocInv T X Y,
      PCategory.assoc_assocInv T X Y, PCategory.assocInv_assoc T X Y⟩
    (PCategory.assoc_p0 T X Y)

def fixedProduct (T X Y : C) : BinaryProduct (constantFamily T X) (constantFamily T Y) where
  obj := tensorConstant (constantFamily T X) Y
  fst := tensorFst (constantFamily T X) Y
  snd := tensorSnd (constantFamily T X) Y
  pair := tensorPair
  fst_total := tensorFst_total _ _
  snd_total := tensorSnd_total _ _
  pair_fst := tensorPair_fst
  pair_snd := tensorPair_snd
  pair_restriction := tensorPair_restriction
  pair_proj := tensorPair_proj

def productIso [Splits C] [CategoryTheory.Limits.HasPullbacks (RestrictionSubobjects.Tot C)]
    (T X Y : C) : constantFamily T (nearProd X Y) ≅
      AmbientSliceProducts.product (constantFamily T X) (constantFamily T Y) :=
  (associatorIso T X Y).symm ≪≫ (fixedProduct T X Y).iso
    ((AmbientSliceProducts.restrictionProducts T).binary (constantFamily T X) (constantFamily T Y))

end CategoricalEssentialIncompleteness.V46.ConstantFamilyProducts
