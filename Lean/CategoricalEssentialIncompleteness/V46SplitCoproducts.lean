/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.RestrictionSplitting

/-! # Binary restriction coproducts in the restriction splitting -/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness.SplitObject

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]
variable [CoprodStruct C] [CategoryTheory.HasCoproducts C] [RestrictionCoproducts C]

/-- Coproducts add the two source restriction idempotents. -/
def binaryCoproduct (X Y : SplitObject C) : SplitObject C :=
  ⟨coprod X.base Y.base, X.domain.sum Y.domain⟩

def binaryCoproductMap {W X Y Z : SplitObject C} (f : W ⟶ X) (g : Y ⟶ Z) :
    binaryCoproduct W Y ⟶ binaryCoproduct X Z :=
  ⟨coprod_map f.hom g.hom, by
    change coprod_map W.domain.hom Y.domain.hom ≫ coprod_map f.hom g.hom = _
    rw [coprod_comp, f.source, g.source], by
    change coprod_map f.hom g.hom ≫ coprod_map X.domain.hom Z.domain.hom = _
    rw [coprod_comp, f.target, g.target]⟩

def binaryCoproductInl (X Y : SplitObject C) : X ⟶ binaryCoproduct X Y :=
  ⟨X.domain.hom ≫ i0 X.base Y.base, by
    change X.domain.hom ≫ (X.domain.hom ≫ i0 X.base Y.base) =
      X.domain.hom ≫ i0 X.base Y.base
    rw [← Category.assoc, X.domain.idem], by
    change (X.domain.hom ≫ i0 X.base Y.base) ≫
      coprod_map X.domain.hom Y.domain.hom = X.domain.hom ≫ i0 X.base Y.base
    rw [Category.assoc, i0_coprod_map, ← Category.assoc, X.domain.idem]⟩

def binaryCoproductInr (X Y : SplitObject C) : Y ⟶ binaryCoproduct X Y :=
  ⟨Y.domain.hom ≫ i1 X.base Y.base, by
    change Y.domain.hom ≫ (Y.domain.hom ≫ i1 X.base Y.base) =
      Y.domain.hom ≫ i1 X.base Y.base
    rw [← Category.assoc, Y.domain.idem], by
    change (Y.domain.hom ≫ i1 X.base Y.base) ≫
      coprod_map X.domain.hom Y.domain.hom = Y.domain.hom ≫ i1 X.base Y.base
    rw [Category.assoc, i1_coprod_map, ← Category.assoc, Y.domain.idem]⟩

def binaryCodiagonal (X : SplitObject C) : binaryCoproduct X X ⟶ X :=
  ⟨copair X.domain.hom X.domain.hom, by
    change coprod_map X.domain.hom X.domain.hom ≫
      copair X.domain.hom X.domain.hom = _
    apply hom_ext
    · rw [← Category.assoc, i0_coprod_map, Category.assoc,
        i0_copair, X.domain.idem]
    · rw [← Category.assoc, i1_coprod_map, Category.assoc,
        i1_copair, X.domain.idem], by
    change copair X.domain.hom X.domain.hom ≫ X.domain.hom =
      copair X.domain.hom X.domain.hom
    rw [copair_comp, X.domain.idem]⟩

instance splitCoprodStruct : CoprodStruct (SplitObject C) where
  coprod := binaryCoproduct
  coprod_map := binaryCoproductMap
  codiag := binaryCodiagonal
  i0 := binaryCoproductInl
  i1 := binaryCoproductInr

@[simp] theorem coproduct_base (X Y : SplitObject C) :
    (coprod X Y).base = coprod X.base Y.base := rfl

@[simp] theorem coproduct_domain (X Y : SplitObject C) :
    (coprod X Y).domain = X.domain.sum Y.domain := rfl

@[simp] theorem coproductMap_hom {W X Y Z : SplitObject C} (f : W ⟶ X) (g : Y ⟶ Z) :
    (coprod_map f g).hom = coprod_map f.hom g.hom := rfl

@[simp] theorem coproductInl_hom (X Y : SplitObject C) :
    (i0 X Y).hom = X.domain.hom ≫ i0 X.base Y.base := rfl

@[simp] theorem coproductInr_hom (X Y : SplitObject C) :
    (i1 X Y).hom = Y.domain.hom ≫ i1 X.base Y.base := rfl

@[simp] theorem codiagonal_hom (X : SplitObject C) :
    (codiag X).hom = copair X.domain.hom X.domain.hom := rfl

instance splitHasCoproducts : CategoryTheory.HasCoproducts (SplitObject C) where
  coprod_id X Y := Hom.ext rfl
  coprod_comp f g h k := Hom.ext (coprod_comp f.hom g.hom h.hom k.hom)
  i0_codiag X := Hom.ext (by
    change (X.domain.hom ≫ i0 X.base X.base) ≫
      copair X.domain.hom X.domain.hom = X.domain.hom
    rw [Category.assoc, i0_copair, X.domain.idem])
  i1_codiag X := Hom.ext (by
    change (X.domain.hom ≫ i1 X.base X.base) ≫
      copair X.domain.hom X.domain.hom = X.domain.hom
    rw [Category.assoc, i1_copair, X.domain.idem])
  i0_i1_codiag X Y := Hom.ext (by
    change coprod_map (X.domain.hom ≫ i0 X.base Y.base)
      (Y.domain.hom ≫ i1 X.base Y.base) ≫
      copair (coprod_map X.domain.hom Y.domain.hom)
        (coprod_map X.domain.hom Y.domain.hom) = coprod_map X.domain.hom Y.domain.hom
    apply hom_ext
    · rw [← Category.assoc, i0_coprod_map, Category.assoc,
        i0_copair, Category.assoc, i0_coprod_map,
        ← Category.assoc, X.domain.idem]
    · rw [← Category.assoc, i1_coprod_map, Category.assoc,
        i1_copair, Category.assoc, i1_coprod_map,
        ← Category.assoc, Y.domain.idem])
  codiag_nat f := Hom.ext (by
    change coprod_map f.hom f.hom ≫ copair _ _ = copair _ _ ≫ f.hom
    apply hom_ext
    · rw [← Category.assoc, i0_coprod_map, Category.assoc,
        i0_copair, ← Category.assoc, i0_copair, f.source, f.target]
    · rw [← Category.assoc, i1_coprod_map, Category.assoc,
        i1_copair, ← Category.assoc, i1_copair, f.source, f.target])
  i0_nat f := Hom.ext (by
    change f.hom ≫ (_ ≫ i0 _ _) = (_ ≫ i0 _ _) ≫ coprod_map f.hom _
    simp only [Category.assoc, i0_coprod_map]
    simp only [← Category.assoc, f.target, f.source])
  i0_nat_right g := Hom.ext (by
    change (_ ≫ i0 _ _) ≫ coprod_map _ g.hom = _ ≫ i0 _ _
    rw [Category.assoc, i0_coprod_map, ← Category.assoc]
    exact congrArg (fun k => k ≫ i0 _ _) (Idem.idem _))
  i1_nat f := Hom.ext (by
    change f.hom ≫ (_ ≫ i1 _ _) = (_ ≫ i1 _ _) ≫ coprod_map _ f.hom
    simp only [Category.assoc, i1_coprod_map]
    simp only [← Category.assoc, f.target, f.source])
  i1_nat_left f := Hom.ext (by
    change (_ ≫ i1 _ _) ≫ coprod_map f.hom _ = _ ≫ i1 _ _
    rw [Category.assoc, i1_coprod_map, ← Category.assoc]
    exact congrArg (fun k => k ≫ i1 _ _) (Idem.idem _))

instance splitRestrictionCoproducts : RestrictionCoproducts (SplitObject C) where
  total_i0 X Y := Hom.ext (by
    change rst (X.domain.hom ≫ i0 X.base Y.base) = X.domain.hom
    rw [rst_comp_of_isTotal _ (RestrictionCoproducts.total_i0 _ _), X.domain.restriction])
  total_i1 X Y := Hom.ext (by
    change rst (Y.domain.hom ≫ i1 X.base Y.base) = Y.domain.hom
    rw [rst_comp_of_isTotal _ (RestrictionCoproducts.total_i1 _ _), Y.domain.restriction])

end CategoricalEssentialIncompleteness.LocalConnectedness.SplitObject
