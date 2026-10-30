/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EffectiveForkSplitting
import CategoricalEssentialIncompleteness.EnumerablePCategory

/-! # Componentwise restriction products on the effective fork -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val)

def product (X Y : Object) : Object where
  center := EnumerableCarriers.product X.center Y.center
  left := EnumerableCarriers.product X.left Y.left
  right := EnumerableCarriers.product X.right Y.right
  leftMap := EnumerableCarriers.partialProdMap X.leftMap Y.leftMap
  rightMap := EnumerableCarriers.partialProdMap X.rightMap Y.rightMap
  left_total := EnumerableCarriers.partialProdMap_total _ _ X.left_total Y.left_total
  right_total := EnumerableCarriers.partialProdMap_total _ _ X.right_total Y.right_total

theorem respects_product {C A D B K L M N : Carrier}
    {r : C ⟶ A} {s : D ⟶ B} {r' : K ⟶ L} {s' : M ⟶ N}
    {f : C ⟶ D} {g : A ⟶ B} {f' : K ⟶ M} {g' : L ⟶ N}
    (h : Respects r s f g) (h' : Respects r' s' f' g') :
    Respects (EnumerableCarriers.partialProdMap r r') (EnumerableCarriers.partialProdMap s s')
      (EnumerableCarriers.partialProdMap f f') (EnumerableCarriers.partialProdMap g g') := by
  intro x y u v hxy hxu hyv
  rw [EnumerableCarriers.mem_partialProdMap_iff] at hxy hxu hyv ⊢
  exact ⟨h _ _ _ _ hxy.1 hxu.1 hyv.1, h' _ _ _ _ hxy.2 hxu.2 hyv.2⟩

def productMap {W X Y Z : Object} (f : W ⟶ X) (g : Y ⟶ Z) : product W Y ⟶ product X Z :=
  ⟨EnumerableCarriers.partialProdMap f.center g.center,
    EnumerableCarriers.partialProdMap f.left g.left,
    EnumerableCarriers.partialProdMap f.right g.right,
    respects_product f.natural_left g.natural_left,
    respects_product f.natural_right g.natural_right⟩

theorem respects_pair {C A D B K L : Carrier} {r : C ⟶ A} {s : D ⟶ B} {t : K ⟶ L}
    {f : C ⟶ D} {g : A ⟶ B} {h : C ⟶ K} {k : A ⟶ L}
    (hf : Respects r s f g) (hh : Respects r t h k) :
    Respects r (EnumerableCarriers.partialProdMap s t)
      (EnumerableCarriers.partialPair f h) (EnumerableCarriers.partialPair g k) := by
  intro x y u v hxy hxu hyv
  rw [EnumerableCarriers.mem_partialPair_iff] at hxy ⊢
  rw [EnumerableCarriers.mem_partialProdMap_iff] at hyv
  exact ⟨hf _ _ _ _ hxy.1 hxu hyv.1, hh _ _ _ _ hxy.2 hxu hyv.2⟩

def partialPair {W X Y : Object} (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ product X Y :=
  ⟨EnumerableCarriers.partialPair f.center g.center,
    EnumerableCarriers.partialPair f.left g.left,
    EnumerableCarriers.partialPair f.right g.right,
    respects_pair f.natural_left g.natural_left, respects_pair f.natural_right g.natural_right⟩

theorem respects_first {C A D B : Carrier} (r : C ⟶ A) (s : D ⟶ B) :
    Respects (EnumerableCarriers.partialProdMap r s) r
      (EnumerableCarriers.partialFst C D) (EnumerableCarriers.partialFst A B) := by
  intro x y u v hxy hxu hyv
  obtain ⟨_, he⟩ := (EnumerableCarriers.mem_partialFst C D x y).mp hxy
  have hu := (EnumerableCarriers.mem_partialProdMap_iff r s x u).mp hxu
  exact (EnumerableCarriers.mem_partialFst A B u v).mpr
    ⟨EnumerableCarriers.val_target _ x u hxu, Part.mem_unique hu.1 (he ▸ hyv)⟩

theorem respects_second {C A D B : Carrier} (r : C ⟶ A) (s : D ⟶ B) :
    Respects (EnumerableCarriers.partialProdMap r s) s
      (EnumerableCarriers.partialSnd C D) (EnumerableCarriers.partialSnd A B) := by
  intro x y u v hxy hxu hyv
  obtain ⟨_, he⟩ := (EnumerableCarriers.mem_partialSnd C D x y).mp hxy
  have hu := (EnumerableCarriers.mem_partialProdMap_iff r s x u).mp hxu
  exact (EnumerableCarriers.mem_partialSnd A B u v).mpr
    ⟨EnumerableCarriers.val_target _ x u hxu, Part.mem_unique hu.2 (he ▸ hyv)⟩

def first (X Y : Object) : product X Y ⟶ X :=
  ⟨EnumerableCarriers.partialFst _ _, EnumerableCarriers.partialFst _ _,
    EnumerableCarriers.partialFst _ _, respects_first _ _, respects_first _ _⟩

def second (X Y : Object) : product X Y ⟶ Y :=
  ⟨EnumerableCarriers.partialSnd _ _, EnumerableCarriers.partialSnd _ _,
    EnumerableCarriers.partialSnd _ _, respects_second _ _, respects_second _ _⟩

def diagonal (X : Object) : X ⟶ product X X := partialPair (𝟙 X) (𝟙 X)

instance : PCategoryStruct Object where
  nearProd := product
  nearProd_map := productMap
  diag := diagonal
  p0 := first
  p1 := second

instance : PCategory Object where
  nearProd_id X Y := Hom.ext (EnumerableCarriers.partialProdMap_id _ _)
    (EnumerableCarriers.partialProdMap_id _ _) (EnumerableCarriers.partialProdMap_id _ _)
  nearProd_comp f g h k := Hom.ext (EnumerableCarriers.partialProdMap_comp _ _ _ _)
    (EnumerableCarriers.partialProdMap_comp _ _ _ _) (EnumerableCarriers.partialProdMap_comp _ _ _ _)
  diag_p0 X := Hom.ext (EnumerableCarriers.partialDiag_fst _)
    (EnumerableCarriers.partialDiag_fst _) (EnumerableCarriers.partialDiag_fst _)
  diag_p1 X := Hom.ext (EnumerableCarriers.partialDiag_snd _)
    (EnumerableCarriers.partialDiag_snd _) (EnumerableCarriers.partialDiag_snd _)
  diag_p0_p1 X Y := Hom.ext (PCategory.diag_p0_p1 X.center Y.center)
    (PCategory.diag_p0_p1 X.left Y.left) (PCategory.diag_p0_p1 X.right Y.right)
  p0_p0 X Y Z := Hom.ext (PCategory.p0_p0 X.center Y.center Z.center)
    (PCategory.p0_p0 X.left Y.left Z.left) (PCategory.p0_p0 X.right Y.right Z.right)
  p0_p1 X Y Z := Hom.ext (PCategory.p0_p1 X.center Y.center Z.center)
    (PCategory.p0_p1 X.left Y.left Z.left) (PCategory.p0_p1 X.right Y.right Z.right)
  p1_p0 X Y Z := Hom.ext (PCategory.p1_p0 X.center Y.center Z.center)
    (PCategory.p1_p0 X.left Y.left Z.left) (PCategory.p1_p0 X.right Y.right Z.right)
  p1_p1 X Y Z := Hom.ext (PCategory.p1_p1 X.center Y.center Z.center)
    (PCategory.p1_p1 X.left Y.left Z.left) (PCategory.p1_p1 X.right Y.right Z.right)
  diag_nat f := Hom.ext (EnumerableCarriers.partialDiag_nat _)
    (EnumerableCarriers.partialDiag_nat _) (EnumerableCarriers.partialDiag_nat _)
  p0_nat f := Hom.ext (PCategory.p0_nat f.center) (PCategory.p0_nat f.left)
    (PCategory.p0_nat f.right)
  p1_nat f := Hom.ext (PCategory.p1_nat f.center) (PCategory.p1_nat f.left)
    (PCategory.p1_nat f.right)
  assoc_nat f g h := Hom.ext (EnumerableCarriers.partialProdMap_assoc_nat _ _ _)
    (EnumerableCarriers.partialProdMap_assoc_nat _ _ _)
    (EnumerableCarriers.partialProdMap_assoc_nat _ _ _)
  swap_nat f g := Hom.ext (EnumerableCarriers.partialProdMap_swap_nat _ _)
    (EnumerableCarriers.partialProdMap_swap_nat _ _) (EnumerableCarriers.partialProdMap_swap_nat _ _)

theorem induced_restriction {X Y : Object} (f : X ⟶ Y) :
    PCategoryStruct.rst f = rst f := Hom.ext (EnumerableCarriers.pcategory_rst_eq _)
  (EnumerableCarriers.pcategory_rst_eq _) (EnumerableCarriers.pcategory_rst_eq _)

instance : RecursionCategory.Prodominical Object where
  nearProd_zero_right f := Hom.ext (RecursionCategory.Prodominical.nearProd_zero_right f.center)
    (RecursionCategory.Prodominical.nearProd_zero_right f.left)
    (RecursionCategory.Prodominical.nearProd_zero_right f.right)
  nearProd_zero_left f := Hom.ext (RecursionCategory.Prodominical.nearProd_zero_left f.center)
    (RecursionCategory.Prodominical.nearProd_zero_left f.left)
    (RecursionCategory.Prodominical.nearProd_zero_left f.right)

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
