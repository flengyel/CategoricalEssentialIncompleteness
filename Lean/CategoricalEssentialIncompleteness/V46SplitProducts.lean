/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.RestrictionSplitting
public import PCats.DomProducts

/-! # Binary restriction products in the restriction splitting

The pairing, projections and their universal property use the existing
restriction structure on `SplitObject`. `V46SplitProductCategory` packages
the product and prodominical laws.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.RestrictionCategory
open PCategoryStruct

namespace CategoricalEssentialIncompleteness.LocalConnectedness.SplitObject

variable {R : Type u} [Category.{v} R] [PCategoryStruct R] [PCategory R]

def productDomain {X Y : R} (a : Idem X) (b : Idem Y) : Idem (nearProd X Y) where
  hom := nearProd_map a.hom b.hom
  restriction := by
    change PCategoryStruct.rst (nearProd_map a.hom b.hom) = nearProd_map a.hom b.hom
    rw [PCategory.rst_nearProd_map,
      show PCategoryStruct.rst a.hom = a.hom from a.restriction,
      show PCategoryStruct.rst b.hom = b.hom from b.restriction]

def binaryProduct (X Y : SplitObject R) : SplitObject R :=
  ⟨nearProd X.base Y.base, productDomain X.domain Y.domain⟩

def binaryProductMap {W X Y Z : SplitObject R} (f : W ⟶ X) (g : Y ⟶ Z) :
    binaryProduct W Y ⟶ binaryProduct X Z :=
  ⟨nearProd_map f.hom g.hom, by
    change nearProd_map W.domain.hom Y.domain.hom ≫ nearProd_map f.hom g.hom = _
    rw [PCategory.nearProd_comp, f.source, g.source], by
    change nearProd_map f.hom g.hom ≫ nearProd_map X.domain.hom Z.domain.hom = _
    rw [PCategory.nearProd_comp, f.target, g.target]⟩

def binaryProductDiagonal (X : SplitObject R) : X ⟶ binaryProduct X X :=
  ⟨X.domain.hom ≫ diag X.base, by
    change X.domain.hom ≫ (X.domain.hom ≫ diag X.base) = X.domain.hom ≫ diag X.base
    rw [← Category.assoc, X.domain.idem], by
    change (X.domain.hom ≫ diag X.base) ≫ nearProd_map X.domain.hom X.domain.hom = _
    rw [Category.assoc, ← PCategory.diag_nat, ← Category.assoc, X.domain.idem]⟩

def binaryProductFst (X Y : SplitObject R) : binaryProduct X Y ⟶ X :=
  ⟨nearProd_map X.domain.hom Y.domain.hom ≫ p0 X.base Y.base, by
    change nearProd_map X.domain.hom Y.domain.hom ≫
      (nearProd_map X.domain.hom Y.domain.hom ≫ p0 X.base Y.base) = _
    rw [← Category.assoc, PCategory.nearProd_comp, X.domain.idem, Y.domain.idem], by
    change (nearProd_map X.domain.hom Y.domain.hom ≫ p0 X.base Y.base) ≫ X.domain.hom = _
    rw [Category.assoc, ← PCategory.p0_nat, ← Category.assoc,
      PCategory.nearProd_comp, X.domain.idem, Category.comp_id]⟩

def binaryProductSnd (X Y : SplitObject R) : binaryProduct X Y ⟶ Y :=
  ⟨nearProd_map X.domain.hom Y.domain.hom ≫ p1 X.base Y.base, by
    change nearProd_map X.domain.hom Y.domain.hom ≫
      (nearProd_map X.domain.hom Y.domain.hom ≫ p1 X.base Y.base) = _
    rw [← Category.assoc, PCategory.nearProd_comp, X.domain.idem, Y.domain.idem], by
    change (nearProd_map X.domain.hom Y.domain.hom ≫ p1 X.base Y.base) ≫ Y.domain.hom = _
    rw [Category.assoc, ← PCategory.p1_nat, ← Category.assoc,
      PCategory.nearProd_comp, Category.comp_id, Y.domain.idem]⟩

@[instance_reducible] def productData : PCategoryStruct (SplitObject R) where
  nearProd := binaryProduct
  nearProd_map := binaryProductMap
  diag := binaryProductDiagonal
  p0 := binaryProductFst
  p1 := binaryProductSnd

/-- The chosen data retain the base product of restriction idempotents. -/
theorem productData_domain (X Y : SplitObject R) :
    ((productData (R := R)).nearProd X Y).domain.hom =
      nearProd_map X.domain.hom Y.domain.hom := rfl

/-- The pairing of partial morphisms has their common domain of definition. -/
def binaryProductPair {W X Y : SplitObject R} (f : W ⟶ X) (g : W ⟶ Y) :
    W ⟶ binaryProduct X Y :=
  ⟨partialPairing f.hom g.hom, by
    rw [PCategory.comp_partialPairing, f.source, g.source], by
    change partialPairing f.hom g.hom ≫ nearProd_map X.domain.hom Y.domain.hom = _
    rw [PCategory.partialPairing_comp_nearProd_map, f.target, g.target]⟩

theorem binaryProductPair_restriction {W X Y : SplitObject R}
    (f : W ⟶ X) (g : W ⟶ Y) :
    rst (binaryProductPair f g) = rst f ≫ rst g := by
  apply Hom.ext
  exact PCategory.rst_partialPairing f.hom g.hom

theorem binaryProductPair_fst {W X Y : SplitObject R}
    (f : W ⟶ X) (g : W ⟶ Y) :
    binaryProductPair f g ≫ binaryProductFst X Y = rst g ≫ f := by
  apply Hom.ext
  change (binaryProductPair f g).hom ≫
    ((binaryProduct X Y).domain.hom ≫ p0 X.base Y.base) = _
  rw [← Category.assoc, (binaryProductPair f g).target]
  exact PCategory.p0_partialPairing f.hom g.hom

theorem binaryProductPair_snd {W X Y : SplitObject R}
    (f : W ⟶ X) (g : W ⟶ Y) :
    binaryProductPair f g ≫ binaryProductSnd X Y = rst f ≫ g := by
  apply Hom.ext
  change (binaryProductPair f g).hom ≫
    ((binaryProduct X Y).domain.hom ≫ p1 X.base Y.base) = _
  rw [← Category.assoc, (binaryProductPair f g).target]
  exact PCategory.p1_partialPairing f.hom g.hom

theorem binaryProductPair_proj {W X Y : SplitObject R}
    (h : W ⟶ binaryProduct X Y) :
    binaryProductPair (h ≫ binaryProductFst X Y)
      (h ≫ binaryProductSnd X Y) = h := by
  apply Hom.ext
  change partialPairing
    (h.hom ≫ ((binaryProduct X Y).domain.hom ≫ p0 X.base Y.base))
    (h.hom ≫ ((binaryProduct X Y).domain.hom ≫ p1 X.base Y.base)) = h.hom
  simp only [← Category.assoc, h.target]
  exact PCategory.partialPairing_proj h.hom

theorem binaryProduct_hom_ext {W X Y : SplitObject R}
    {h k : W ⟶ binaryProduct X Y}
    (h0 : h ≫ binaryProductFst X Y = k ≫ binaryProductFst X Y)
    (h1 : h ≫ binaryProductSnd X Y = k ≫ binaryProductSnd X Y) : h = k := by
  rw [← binaryProductPair_proj h, ← binaryProductPair_proj k, h0, h1]

/-- Binary products in the total subcategory, with arbitrary split apex. -/
theorem binaryProduct_existsUnique {W X Y : SplitObject R}
    (f : W ⟶ X) (g : W ⟶ Y) (hf : isTotal f) (hg : isTotal g) :
    ∃! h : W ⟶ binaryProduct X Y,
      isTotal h ∧ h ≫ binaryProductFst X Y = f ∧ h ≫ binaryProductSnd X Y = g := by
  refine ⟨binaryProductPair f g, ⟨?_, ?_, ?_⟩, ?_⟩
  · change rst (binaryProductPair f g) = 𝟙 W
    rw [binaryProductPair_restriction, hf, hg, Category.id_comp]
  · rw [binaryProductPair_fst, hg, Category.id_comp]
  · rw [binaryProductPair_snd, hf, Category.id_comp]
  · rintro h ⟨_, h0, h1⟩
    apply binaryProduct_hom_ext
    · rw [h0, binaryProductPair_fst, hg, Category.id_comp]
    · rw [h1, binaryProductPair_snd, hf, Category.id_comp]

theorem binaryProductFst_total (X Y : SplitObject R) :
    isTotal (binaryProductFst X Y) := by
  apply Hom.ext
  change PCategoryStruct.rst
    (nearProd_map X.domain.hom Y.domain.hom ≫ p0 X.base Y.base) =
      nearProd_map X.domain.hom Y.domain.hom
  rw [PCategory.rst_comp_of_isTotal' _ (PCategory.p0_isTotal _ _),
    PCategory.rst_nearProd_map,
    show PCategoryStruct.rst X.domain.hom = X.domain.hom from X.domain.restriction,
    show PCategoryStruct.rst Y.domain.hom = Y.domain.hom from Y.domain.restriction]

theorem binaryProductSnd_total (X Y : SplitObject R) :
    isTotal (binaryProductSnd X Y) := by
  apply Hom.ext
  change PCategoryStruct.rst
    (nearProd_map X.domain.hom Y.domain.hom ≫ p1 X.base Y.base) =
      nearProd_map X.domain.hom Y.domain.hom
  rw [PCategory.rst_comp_of_isTotal' _ (PCategory.p1_isTotal _ _),
    PCategory.rst_nearProd_map,
    show PCategoryStruct.rst X.domain.hom = X.domain.hom from X.domain.restriction,
    show PCategoryStruct.rst Y.domain.hom = Y.domain.hom from Y.domain.restriction]

theorem comp_binaryProductPair {V W X Y : SplitObject R}
    (h : V ⟶ W) (f : W ⟶ X) (g : W ⟶ Y) :
    h ≫ binaryProductPair f g = binaryProductPair (h ≫ f) (h ≫ g) :=
  Hom.ext (PCategory.comp_partialPairing h.hom f.hom g.hom)

theorem binaryProductPair_comp_map {V W X Y Z : SplitObject R}
    (f : V ⟶ W) (g : V ⟶ X) (a : W ⟶ Y) (b : X ⟶ Z) :
    binaryProductPair f g ≫ binaryProductMap a b =
      binaryProductPair (f ≫ a) (g ≫ b) :=
  Hom.ext (PCategory.partialPairing_comp_nearProd_map f.hom g.hom a.hom b.hom)

theorem productData_partialPairing {W X Y : SplitObject R}
    (f : W ⟶ X) (g : W ⟶ Y) :
    @PCategoryStruct.partialPairing (SplitObject R) inferInstance productData W X Y f g =
      binaryProductPair f g := by
  apply Hom.ext
  change (W.domain.hom ≫ diag W.base) ≫ nearProd_map f.hom g.hom =
    partialPairing f.hom g.hom
  rw [Category.assoc]
  exact (binaryProductPair f g).source

/-- The chosen product data induce the existing restriction operation. -/
theorem productData_restriction {X Y : SplitObject R} (f : X ⟶ Y) :
    @PCategoryStruct.rst (SplitObject R) inferInstance productData X Y f = rst f := by
  unfold PCategoryStruct.rst
  rw [← Category.assoc]
  change (@PCategoryStruct.partialPairing (SplitObject R) inferInstance productData
    X X Y (𝟙 X) f) ≫ binaryProductFst X Y = rst f
  rw [productData_partialPairing, binaryProductPair_fst, Category.comp_id]

end CategoricalEssentialIncompleteness.LocalConnectedness.SplitObject
