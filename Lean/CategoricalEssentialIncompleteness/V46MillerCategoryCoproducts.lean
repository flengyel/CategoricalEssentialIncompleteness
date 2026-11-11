/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCategoryProducts

/-! # Tagged restriction coproducts with one common oracle program -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoryTheory.CoprodStruct
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
variable {z : Family}
attribute [instance 2000] nativeRestriction

@[implicit_reducible] def coproduct (X Y : Object z) : Object z := ⟨.coproduct X.type Y.type⟩

def copairRaw {X Y Z : Object z} (f : X ⟶ Z) (g : Y ⟶ Z) : coproduct X Y ⟶ Z :=
  ⟨Sum.elim f.val g.val,Represented.sum f.represented g.represented⟩

def inl (X Y : Object z) : X ⟶ coproduct X Y := totalFromFunction Sum.inl Computable.sumInl
def inr (X Y : Object z) : Y ⟶ coproduct X Y := totalFromFunction Sum.inr Computable.sumInr

def sumMap {W X Y Z : Object z} (f : W ⟶ X) (g : Y ⟶ Z) : coproduct W Y ⟶ coproduct X Z :=
  copairRaw (f ≫ inl X Z) (g ≫ inr X Z)

def codiagonal (X : Object z) : coproduct X X ⟶ X :=
  totalFromFunction (Sum.elim id id) (Computable.sumCasesOn Computable.id Computable.snd.to₂ Computable.snd.to₂)

instance coproductStruct : CoprodStruct (Object z) where
  coprod := coproduct
  coprod_map := sumMap
  codiag := codiagonal
  i0 := inl
  i1 := inr

@[simp] theorem inl_val (X Y : Object z) : (inl X Y).val=fun x => Part.some (Sum.inl x) := rfl
@[simp] theorem inr_val (X Y : Object z) : (inr X Y).val=fun y => Part.some (Sum.inr y) := rfl
@[simp] theorem codiagonal_val (X : Object z) :
    (codiagonal X).val=fun s => Part.some (s.elim id id) := rfl

theorem sumMap_val {W X Y Z : Object z} (f : W ⟶ X) (g : Y ⟶ Z) :
    (sumMap f g).val=PartialFunctions.sumMap f.val g.val := by
  funext s
  cases s <;> simp only [sumMap,copairRaw,comp_val,inl_val,inr_val,
    Part.bind_some_eq_map,PartialFunctions.sumMap]

theorem coproduct_map_val {W X Y Z : Object z} (f : W ⟶ X) (g : Y ⟶ Z) :
    (coprod_map f g).val=coprod_map (C := PartialFunctions.Pfn) f.val g.val := sumMap_val f g

@[simp] theorem i0_val (X Y : Object z) :
    (i0 X Y).val=fun x => Part.some (Sum.inl x) := rfl
@[simp] theorem i1_val (X Y : Object z) :
    (i1 X Y).val=fun y => Part.some (Sum.inr y) := rfl
@[simp] theorem codiag_val (X : Object z) :
    (CoprodStruct.codiag X).val=fun s => Part.some (s.elim id id) := rfl
@[simp] theorem coprod_map_rawVal {W X Y Z : Object z} (f : W ⟶ X) (g : Y ⟶ Z) :
    (coprod_map f g).val=PartialFunctions.sumMap f.val g.val := sumMap_val f g

instance coproducts : CategoryTheory.HasCoproducts (Object z) where
  coprod_id X Y := by
    apply Arrow.ext
    change (sumMap (𝟙 X) (𝟙 Y)).val=(𝟙 (coproduct X Y) : coproduct X Y ⟶ coproduct X Y).val
    rw [sumMap_val,id_val,id_val,id_val]
    exact CategoryTheory.HasCoproducts.coprod_id (C := PartialFunctions.Pfn)
      ((inclusion z).obj X) ((inclusion z).obj Y)
  coprod_comp f g h k := by
    apply Arrow.ext
    simp only [comp_val,coproduct_map_val]
    exact CategoryTheory.HasCoproducts.coprod_comp (C := PartialFunctions.Pfn) f.val g.val h.val k.val
  i0_codiag X := by
    apply Arrow.ext
    change ((inl X X) ≫ codiagonal X).val=(𝟙 X : X ⟶ X).val
    simp only [comp_val,inl_val,codiagonal_val,id_val,Part.bind_some]
    rfl
  i1_codiag X := by
    apply Arrow.ext
    change ((inr X X) ≫ codiagonal X).val=(𝟙 X : X ⟶ X).val
    simp only [comp_val,inr_val,codiagonal_val,id_val,Part.bind_some]
    rfl
  i0_i1_codiag X Y := by
    apply Arrow.ext
    funext s
    cases s <;> simp [coprod_map_rawVal,i0_val,i1_val,codiag_val,comp_val,
      id_val,PartialFunctions.sumMap]
  codiag_nat f := by
    apply Arrow.ext
    funext s
    cases s <;> simp [coprod_map_rawVal,codiag_val,comp_val,PartialFunctions.sumMap,
      Part.bind_some_eq_map]
    all_goals rw [Part.map_map]; exact Part.map_id' (fun _ => rfl) _
  i0_nat f := by
    apply Arrow.ext
    funext x
    simp [coprod_map_rawVal,i0_val,comp_val,PartialFunctions.sumMap,Part.bind_some_eq_map]
  i0_nat_right g := by
    apply Arrow.ext
    funext x
    simp [coprod_map_rawVal,i0_val,comp_val,id_val,PartialFunctions.sumMap]
  i1_nat f := by
    apply Arrow.ext
    funext x
    simp [coprod_map_rawVal,i1_val,comp_val,PartialFunctions.sumMap,Part.bind_some_eq_map]
  i1_nat_left f := by
    apply Arrow.ext
    funext x
    simp [coprod_map_rawVal,i1_val,comp_val,id_val,PartialFunctions.sumMap]

instance restrictionCoproducts : RestrictionCoproducts (Object z) where
  total_i0 X Y := totalFromFunction_total (X := X) (Y := coproduct X Y)
    Sum.inl Computable.sumInl
  total_i1 X Y := totalFromFunction_total (X := Y) (Y := coproduct X Y)
    Sum.inr Computable.sumInr

end CategoricalEssentialIncompleteness.V46.Miller.Uniform
