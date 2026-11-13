/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SplitProducts
public import PCats.Recursion

/-! # The product and prodominical laws in the restriction splitting -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.RestrictionCategory
open PCategoryStruct

namespace CategoricalEssentialIncompleteness.LocalConnectedness.SplitObject

variable {R : Type u} [Category.{v} R] [PCategoryStruct R] [PCategory R]

attribute [local instance] productData

theorem comp_binaryProductFst_hom {W X Y : SplitObject R}
    (h : W ⟶ binaryProduct X Y) :
    (h ≫ binaryProductFst X Y).hom = h.hom ≫ p0 X.base Y.base := by
  change h.hom ≫ ((binaryProduct X Y).domain.hom ≫ p0 X.base Y.base) = _
  rw [← Category.assoc, h.target]

theorem comp_binaryProductSnd_hom {W X Y : SplitObject R}
    (h : W ⟶ binaryProduct X Y) :
    (h ≫ binaryProductSnd X Y).hom = h.hom ≫ p1 X.base Y.base := by
  change h.hom ≫ ((binaryProduct X Y).domain.hom ≫ p1 X.base Y.base) = _
  rw [← Category.assoc, h.target]

theorem productData_assoc_hom (X Y Z : SplitObject R) :
    (assoc X Y Z).hom = (binaryProduct (binaryProduct X Y) Z).domain.hom ≫
      assoc X.base Y.base Z.base := by
  unfold assoc
  rw [productData_partialPairing, productData_partialPairing]
  change partialPairing
    ((binaryProductFst (binaryProduct X Y) Z ≫ binaryProductFst X Y).hom)
    (partialPairing
      ((binaryProductFst (binaryProduct X Y) Z ≫ binaryProductSnd X Y).hom)
      (binaryProductSnd (binaryProduct X Y) Z).hom) = _
  rw [comp_binaryProductFst_hom, comp_binaryProductSnd_hom]
  change partialPairing
    (((binaryProduct (binaryProduct X Y) Z).domain.hom ≫
      p0 (nearProd X.base Y.base) Z.base) ≫ p0 X.base Y.base)
    (partialPairing
      (((binaryProduct (binaryProduct X Y) Z).domain.hom ≫
        p0 (nearProd X.base Y.base) Z.base) ≫ p1 X.base Y.base)
      ((binaryProduct (binaryProduct X Y) Z).domain.hom ≫
        p1 (nearProd X.base Y.base) Z.base)) = _
  simp only [Category.assoc, ← PCategory.comp_partialPairing]

theorem productData_swap_hom (X Y : SplitObject R) :
    (swap X Y).hom = (binaryProduct X Y).domain.hom ≫ swap X.base Y.base := by
  unfold swap
  rw [productData_partialPairing]
  change partialPairing
    ((binaryProduct X Y).domain.hom ≫ p1 X.base Y.base)
    ((binaryProduct X Y).domain.hom ≫ p0 X.base Y.base) = _
  rw [← PCategory.comp_partialPairing]

/-- The chosen binary products satisfy all the `P`-category laws. -/
theorem productLaws : PCategory (SplitObject R) where
  nearProd_id X Y := Hom.ext rfl
  nearProd_comp f g h k := Hom.ext (PCategory.nearProd_comp f.hom g.hom h.hom k.hom)
  diag_p0 X := by
    apply Hom.ext
    change (binaryProductDiagonal X ≫ binaryProductFst X X).hom = _
    rw [comp_binaryProductFst_hom]
    change (X.domain.hom ≫ diag X.base) ≫ p0 X.base X.base = X.domain.hom
    rw [Category.assoc, PCategory.diag_p0, Category.comp_id]
  diag_p1 X := by
    apply Hom.ext
    change (binaryProductDiagonal X ≫ binaryProductSnd X X).hom = _
    rw [comp_binaryProductSnd_hom]
    change (X.domain.hom ≫ diag X.base) ≫ p1 X.base X.base = X.domain.hom
    rw [Category.assoc, PCategory.diag_p1, Category.comp_id]
  diag_p0_p1 X Y := by
    change partialPairing (binaryProductFst X Y) (binaryProductSnd X Y) = 𝟙 _
    rw [productData_partialPairing]
    simpa only [Category.id_comp] using binaryProductPair_proj (𝟙 (binaryProduct X Y))
  p0_p0 X Y Z := by
    apply Hom.ext
    change (binaryProductMap (𝟙 X) (binaryProductFst Y Z) ≫
      binaryProductFst X Y).hom = _
    rw [comp_binaryProductFst_hom]
    change nearProd_map X.domain.hom
      (nearProd_map Y.domain.hom Z.domain.hom ≫ p0 Y.base Z.base) ≫ p0 X.base Y.base =
        nearProd_map X.domain.hom (nearProd_map Y.domain.hom Z.domain.hom) ≫
          p0 X.base (nearProd Y.base Z.base)
    calc
      _ = (nearProd_map X.domain.hom (nearProd_map Y.domain.hom Z.domain.hom) ≫
          nearProd_map (𝟙 X.base) (p0 Y.base Z.base)) ≫ p0 X.base Y.base := by
        rw [PCategory.nearProd_comp, Category.comp_id]
      _ = _ := by rw [Category.assoc, PCategory.p0_p0]
  p0_p1 X Y Z := by
    apply Hom.ext
    change (binaryProductMap (𝟙 X) (binaryProductSnd Y Z) ≫
      binaryProductFst X Z).hom = _
    rw [comp_binaryProductFst_hom]
    change nearProd_map X.domain.hom
      (nearProd_map Y.domain.hom Z.domain.hom ≫ p1 Y.base Z.base) ≫ p0 X.base Z.base =
        nearProd_map X.domain.hom (nearProd_map Y.domain.hom Z.domain.hom) ≫
          p0 X.base (nearProd Y.base Z.base)
    calc
      _ = (nearProd_map X.domain.hom (nearProd_map Y.domain.hom Z.domain.hom) ≫
          nearProd_map (𝟙 X.base) (p1 Y.base Z.base)) ≫ p0 X.base Z.base := by
        rw [PCategory.nearProd_comp, Category.comp_id]
      _ = _ := by rw [Category.assoc, PCategory.p0_p1]
  p1_p0 X Y Z := by
    apply Hom.ext
    change (binaryProductMap (binaryProductFst X Y) (𝟙 Z) ≫
      binaryProductSnd X Z).hom = _
    rw [comp_binaryProductSnd_hom]
    change nearProd_map
      (nearProd_map X.domain.hom Y.domain.hom ≫ p0 X.base Y.base) Z.domain.hom ≫
        p1 X.base Z.base =
      nearProd_map (nearProd_map X.domain.hom Y.domain.hom) Z.domain.hom ≫
        p1 (nearProd X.base Y.base) Z.base
    calc
      _ = (nearProd_map (nearProd_map X.domain.hom Y.domain.hom) Z.domain.hom ≫
          nearProd_map (p0 X.base Y.base) (𝟙 Z.base)) ≫ p1 X.base Z.base := by
        rw [PCategory.nearProd_comp, Category.comp_id]
      _ = _ := by rw [Category.assoc, PCategory.p1_p0]
  p1_p1 X Y Z := by
    apply Hom.ext
    change (binaryProductMap (binaryProductSnd X Y) (𝟙 Z) ≫
      binaryProductSnd Y Z).hom = _
    rw [comp_binaryProductSnd_hom]
    change nearProd_map
      (nearProd_map X.domain.hom Y.domain.hom ≫ p1 X.base Y.base) Z.domain.hom ≫
        p1 Y.base Z.base =
      nearProd_map (nearProd_map X.domain.hom Y.domain.hom) Z.domain.hom ≫
        p1 (nearProd X.base Y.base) Z.base
    calc
      _ = (nearProd_map (nearProd_map X.domain.hom Y.domain.hom) Z.domain.hom ≫
          nearProd_map (p1 X.base Y.base) (𝟙 Z.base)) ≫ p1 Y.base Z.base := by
        rw [PCategory.nearProd_comp, Category.comp_id]
      _ = _ := by rw [Category.assoc, PCategory.p1_p1]
  diag_nat {X Y} f := by
    apply Hom.ext
    change f.hom ≫ (Y.domain.hom ≫ diag Y.base) =
      (X.domain.hom ≫ diag X.base) ≫ nearProd_map f.hom f.hom
    rw [← Category.assoc, f.target, Category.assoc, ← PCategory.diag_nat,
      ← Category.assoc, f.source]
  p0_nat {X Y Z} f := by
    apply Hom.ext
    change (binaryProductMap f (𝟙 Z) ≫ binaryProductFst Y Z).hom = _
    rw [comp_binaryProductFst_hom]
    change nearProd_map f.hom Z.domain.hom ≫ p0 Y.base Z.base =
      (nearProd_map X.domain.hom Z.domain.hom ≫ p0 X.base Z.base) ≫ f.hom
    calc
      _ = (nearProd_map X.domain.hom Z.domain.hom ≫
          nearProd_map f.hom (𝟙 Z.base)) ≫ p0 Y.base Z.base := by
        rw [PCategory.nearProd_comp, f.source, Category.comp_id]
      _ = _ := by rw [Category.assoc, PCategory.p0_nat, ← Category.assoc]
  p1_nat {X Y Z} f := by
    apply Hom.ext
    change (binaryProductMap (𝟙 Z) f ≫ binaryProductSnd Z Y).hom = _
    rw [comp_binaryProductSnd_hom]
    change nearProd_map Z.domain.hom f.hom ≫ p1 Z.base Y.base =
      (nearProd_map Z.domain.hom X.domain.hom ≫ p1 Z.base X.base) ≫ f.hom
    calc
      _ = (nearProd_map Z.domain.hom X.domain.hom ≫
          nearProd_map (𝟙 Z.base) f.hom) ≫ p1 Z.base Y.base := by
        rw [PCategory.nearProd_comp, f.source, Category.comp_id]
      _ = _ := by rw [Category.assoc, PCategory.p1_nat, ← Category.assoc]
  assoc_nat {X X' Y Y' Z Z'} f g h := by
    apply Hom.ext
    simp only [comp_hom, productData_assoc_hom]
    change (binaryProductMap (binaryProductMap f g) h).hom ≫
      ((binaryProduct (binaryProduct X' Y') Z').domain.hom ≫
        assoc X'.base Y'.base Z'.base) = _
    rw [← Category.assoc, (binaryProductMap (binaryProductMap f g) h).target]
    change nearProd_map (nearProd_map f.hom g.hom) h.hom ≫
      assoc X'.base Y'.base Z'.base =
      ((binaryProduct (binaryProduct X Y) Z).domain.hom ≫ assoc X.base Y.base Z.base) ≫
        nearProd_map f.hom (nearProd_map g.hom h.hom)
    rw [Category.assoc, ← PCategory.assoc_nat, ← Category.assoc]
    exact congrArg (fun k => k ≫ assoc X'.base Y'.base Z'.base)
      (binaryProductMap (binaryProductMap f g) h).source.symm
  swap_nat {X X' Y Y'} f g := by
    apply Hom.ext
    simp only [comp_hom, productData_swap_hom]
    change (binaryProductMap f g).hom ≫
      ((binaryProduct X' Y').domain.hom ≫ swap X'.base Y'.base) = _
    rw [← Category.assoc, (binaryProductMap f g).target]
    change nearProd_map f.hom g.hom ≫ swap X'.base Y'.base =
      ((binaryProduct X Y).domain.hom ≫ swap X.base Y.base) ≫ nearProd_map g.hom f.hom
    rw [Category.assoc, ← PCategory.swap_nat, ← Category.assoc]
    exact congrArg (fun k => k ≫ swap X'.base Y'.base) (binaryProductMap f g).source.symm

variable [CategoryTheory.Limits.HasZeroMorphisms R] [RecursionCategory.Prodominical R]

/-- Zero absorption is inherited by products of split objects. -/
theorem prodominicalLaws : RecursionCategory.Prodominical (SplitObject R) where
  nearProd_zero_right f := Hom.ext (RecursionCategory.Prodominical.nearProd_zero_right f.hom)
  nearProd_zero_left f := Hom.ext (RecursionCategory.Prodominical.nearProd_zero_left f.hom)

end CategoricalEssentialIncompleteness.LocalConnectedness.SplitObject
