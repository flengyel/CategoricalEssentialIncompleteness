/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EffectiveForkProducts
public import CategoricalEssentialIncompleteness.EffectiveForkTotal
public import CategoricalEssentialIncompleteness.EnumerableCoproducts

/-! # Tagged restriction coproducts on the effective fork -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.CoprodStruct

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val)

def coproduct (X Y : Object) : Object where
  center := coprod X.center Y.center
  left := coprod X.left Y.left
  right := coprod X.right Y.right
  leftMap := coprod_map X.leftMap Y.leftMap
  rightMap := coprod_map X.rightMap Y.rightMap
  left_total := EnumerableCarriers.coproductMap_total _ _ X.left_total Y.left_total
  right_total := EnumerableCarriers.coproductMap_total _ _ X.right_total Y.right_total

theorem respects_coproduct {C A D B K L M N : Carrier}
    {r : C ⟶ A} {s : D ⟶ B} {r' : K ⟶ L} {s' : M ⟶ N}
    {f : C ⟶ D} {g : A ⟶ B} {f' : K ⟶ M} {g' : L ⟶ N}
    (h : Respects r s f g) (h' : Respects r' s' f' g') :
    Respects (coprod_map r r') (coprod_map s s') (coprod_map f f') (coprod_map g g') := by
  intro x y u v hxy hxu hyv
  by_cases he : x%2=0
  · have hx : x=2*(x/2) := by omega
    rw [hx, EnumerableCarriers.val_map_even] at hxy hxu
    obtain ⟨y0, hy0, hye⟩ := (Part.mem_map_iff _).mp hxy
    obtain ⟨u0, hu0, hue⟩ := (Part.mem_map_iff _).mp hxu
    rw [← hye, EnumerableCarriers.val_map_even] at hyv
    rw [← hue, EnumerableCarriers.val_map_even]
    obtain ⟨v0, hv0, hve⟩ := (Part.mem_map_iff _).mp hyv
    exact (Part.mem_map_iff _).mpr ⟨v0, h _ _ _ _ hy0 hu0 hv0, hve⟩
  · have hx : x=2*(x/2)+1 := by omega
    rw [hx, EnumerableCarriers.val_map_odd] at hxy hxu
    obtain ⟨y0, hy0, hye⟩ := (Part.mem_map_iff _).mp hxy
    obtain ⟨u0, hu0, hue⟩ := (Part.mem_map_iff _).mp hxu
    rw [← hye, EnumerableCarriers.val_map_odd] at hyv
    rw [← hue, EnumerableCarriers.val_map_odd]
    obtain ⟨v0, hv0, hve⟩ := (Part.mem_map_iff _).mp hyv
    exact (Part.mem_map_iff _).mpr ⟨v0, h' _ _ _ _ hy0 hu0 hv0, hve⟩

def coproductMap {W X Y Z : Object} (f : W ⟶ X) (g : Y ⟶ Z) :
    coproduct W Y ⟶ coproduct X Z :=
  ⟨coprod_map f.center g.center, coprod_map f.left g.left, coprod_map f.right g.right,
    respects_coproduct f.natural_left g.natural_left,
    respects_coproduct f.natural_right g.natural_right⟩

def inl (X Y : Object) : X ⟶ coproduct X Y :=
  ⟨i0 _ _, i0 _ _, i0 _ _,
    respects_of_eq (EnumerableCarriers.inl_map X.leftMap Y.leftMap).symm,
    respects_of_eq (EnumerableCarriers.inl_map X.rightMap Y.rightMap).symm⟩

def inr (X Y : Object) : Y ⟶ coproduct X Y :=
  ⟨i1 _ _, i1 _ _, i1 _ _,
    respects_of_eq (EnumerableCarriers.inr_map X.leftMap Y.leftMap).symm,
    respects_of_eq (EnumerableCarriers.inr_map X.rightMap Y.rightMap).symm⟩

def codiagonal (X : Object) : coproduct X X ⟶ X :=
  ⟨codiag _, codiag _, codiag _,
    respects_of_eq (CategoryTheory.HasCoproducts.codiag_nat X.leftMap),
    respects_of_eq (CategoryTheory.HasCoproducts.codiag_nat X.rightMap)⟩

instance : CoprodStruct Object where
  coprod := coproduct
  coprod_map := coproductMap
  i0 := inl
  i1 := inr
  codiag := codiagonal

instance : CategoryTheory.HasCoproducts Object where
  coprod_id X Y := Hom.ext (CategoryTheory.HasCoproducts.coprod_id X.center Y.center)
    (CategoryTheory.HasCoproducts.coprod_id X.left Y.left)
    (CategoryTheory.HasCoproducts.coprod_id X.right Y.right)
  coprod_comp f g h k := Hom.ext (CategoryTheory.HasCoproducts.coprod_comp _ _ _ _)
    (CategoryTheory.HasCoproducts.coprod_comp _ _ _ _)
    (CategoryTheory.HasCoproducts.coprod_comp _ _ _ _)
  i0_codiag X := Hom.ext (CategoryTheory.HasCoproducts.i0_codiag X.center)
    (CategoryTheory.HasCoproducts.i0_codiag X.left)
    (CategoryTheory.HasCoproducts.i0_codiag X.right)
  i1_codiag X := Hom.ext (CategoryTheory.HasCoproducts.i1_codiag X.center)
    (CategoryTheory.HasCoproducts.i1_codiag X.left)
    (CategoryTheory.HasCoproducts.i1_codiag X.right)
  i0_i1_codiag X Y := Hom.ext (CategoryTheory.HasCoproducts.i0_i1_codiag X.center Y.center)
    (CategoryTheory.HasCoproducts.i0_i1_codiag X.left Y.left)
    (CategoryTheory.HasCoproducts.i0_i1_codiag X.right Y.right)
  codiag_nat f := Hom.ext (CategoryTheory.HasCoproducts.codiag_nat f.center)
    (CategoryTheory.HasCoproducts.codiag_nat f.left) (CategoryTheory.HasCoproducts.codiag_nat f.right)
  i0_nat f := Hom.ext (CategoryTheory.HasCoproducts.i0_nat f.center)
    (CategoryTheory.HasCoproducts.i0_nat f.left) (CategoryTheory.HasCoproducts.i0_nat f.right)
  i0_nat_right f := Hom.ext (CategoryTheory.HasCoproducts.i0_nat_right f.center)
    (CategoryTheory.HasCoproducts.i0_nat_right f.left)
    (CategoryTheory.HasCoproducts.i0_nat_right f.right)
  i1_nat f := Hom.ext (CategoryTheory.HasCoproducts.i1_nat f.center)
    (CategoryTheory.HasCoproducts.i1_nat f.left) (CategoryTheory.HasCoproducts.i1_nat f.right)
  i1_nat_left f := Hom.ext (CategoryTheory.HasCoproducts.i1_nat_left f.center)
    (CategoryTheory.HasCoproducts.i1_nat_left f.left) (CategoryTheory.HasCoproducts.i1_nat_left f.right)

instance : RestrictionCoproducts Object where
  total_i0 X Y := (total_iff _).mpr ⟨RestrictionCoproducts.total_i0 _ _,
    RestrictionCoproducts.total_i0 _ _, RestrictionCoproducts.total_i0 _ _⟩
  total_i1 X Y := (total_iff _).mpr ⟨RestrictionCoproducts.total_i1 _ _,
    RestrictionCoproducts.total_i1 _ _, RestrictionCoproducts.total_i1 _ _⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
