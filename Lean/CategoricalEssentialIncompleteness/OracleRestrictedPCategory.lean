/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.OracleRestrictedProducts

/-! # The prodominical P-category of oracle-domain restrictions -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted

variable {S : Set ℕ}
attribute [instance 2000] nativeRestriction

@[simp] theorem mem_id (X : Restricted S) (x y : carrier S X) :
    y ∈ (𝟙 X : X ⟶ X).val x ↔ y=x := Part.mem_some_iff

@[simp] theorem zero_val (X Y : Restricted S) : (0 : X ⟶ Y).val=fun _ => Part.none := rfl

theorem hom_ext_mem {X Y : Restricted S} {f g : X ⟶ Y}
    (h : ∀ x y,y ∈ f.val x ↔ y ∈ g.val x) : f=g :=
  Arrow.ext (funext (fun x => Part.ext (h x)))

theorem productMap_id (X Y : Restricted S) : productMap (𝟙 X) (𝟙 Y)=𝟙 (product X Y) := by
  apply hom_ext_mem
  intro p q
  simp only [mem_productMap,mem_id]
  change (q.1=p.1 ∧ q.2=p.2) ↔ q=p
  exact Prod.ext_iff.symm

theorem diagonal_first (X : Restricted S) : diagonal X ≫ first X X=𝟙 X := by
  apply hom_ext_mem
  intro x y
  simp only [mem_comp,mem_diagonal,mem_first,mem_id,exists_eq_left]

theorem diagonal_second (X : Restricted S) : diagonal X ≫ second X X=𝟙 X := by
  apply hom_ext_mem
  intro x y
  simp only [mem_comp,mem_diagonal,mem_second,mem_id,exists_eq_left]

theorem diagonal_productMap {W X Y : Restricted S} (f : W ⟶ X) (g : W ⟶ Y) :
    diagonal W ≫ productMap f g=pairing f g := by
  apply hom_ext_mem
  intro w q
  rcases q with ⟨x,y⟩
  simp only [comp_val,diagonal_val,productMap_val,pairing_val,Part.bind_some,rawPair]

instance pcategoryStruct : PCategoryStruct (Restricted S) where
  nearProd := product
  nearProd_map := productMap
  diag := diagonal
  p0 := first
  p1 := second

@[simp] theorem p0_eq_first (X Y : Restricted S) : PCategoryStruct.p0 X Y=first X Y := rfl
@[simp] theorem p1_eq_second (X Y : Restricted S) : PCategoryStruct.p1 X Y=second X Y := rfl

theorem pcategory_pairing_eq {W X Y : Restricted S} (f : W ⟶ X) (g : W ⟶ Y) :
    PCategoryStruct.partialPairing f g=pairing f g := diagonal_productMap f g

theorem associator_val (X Y Z : Restricted S) :
    (PCategoryStruct.assoc X Y Z).val=fun p => Part.some (p.1.1,(p.1.2,p.2)) := by
  rw [PCategoryStruct.assoc,pcategory_pairing_eq,pcategory_pairing_eq]
  funext p
  simp only [pairing_val,rawPair,comp_val,p0_eq_first,p1_eq_second,first_val,second_val,Part.bind_some,Part.map_some]

theorem swap_val (X Y : Restricted S) :
    (PCategoryStruct.swap X Y).val=fun p => Part.some (p.2,p.1) := by
  rw [PCategoryStruct.swap,pcategory_pairing_eq]
  funext p
  simp only [pairing_val,rawPair,p0_eq_first,p1_eq_second,first_val,second_val,Part.bind_some,Part.map_some]

theorem mem_associator (X Y Z : Restricted S)
    (p : carrier S (product (product X Y) Z)) (q : carrier S (product X (product Y Z))) :
    q ∈ (PCategoryStruct.assoc X Y Z).val p ↔ q=(p.1.1,(p.1.2,p.2)) := by
  rw [associator_val]
  exact Part.mem_some_iff

theorem mem_swap (X Y : Restricted S) (p : carrier S (product X Y)) (q : carrier S (product Y X)) :
    q ∈ (PCategoryStruct.swap X Y).val p ↔ q=(p.2,p.1) := by
  rw [swap_val]
  exact Part.mem_some_iff

instance pcategory : PCategory (Restricted S) where
  nearProd_id := productMap_id
  nearProd_comp := productMap_comp
  diag_p0 := diagonal_first
  diag_p1 := diagonal_second
  diag_p0_p1 X Y := by
    change diagonal (product X Y) ≫ productMap (first X Y) (second X Y)=𝟙 _
    rw [diagonal_productMap]
    apply Arrow.ext
    funext p
    simp only [pairing_val,rawPair,first_val,second_val,id_val,Part.bind_some,Part.map_some]
    rcases p with ⟨x,y⟩
    rfl
  p0_p0 X Y Z := by
    change productMap (𝟙 X) (first Y Z) ≫ first X Y=first X (product Y Z)
    apply Arrow.ext
    funext p
    simp only [comp_val,productMap_val,id_val,first_val,second_val,Part.bind_some,Part.map_some]
  p0_p1 X Y Z := by
    change productMap (𝟙 X) (second Y Z) ≫ first X Z=first X (product Y Z)
    apply Arrow.ext
    funext p
    simp only [comp_val,productMap_val,id_val,first_val,second_val,Part.bind_some,Part.map_some]
  p1_p0 X Y Z := by
    change productMap (first X Y) (𝟙 Z) ≫ second X Z=second (product X Y) Z
    apply Arrow.ext
    funext p
    simp only [comp_val,productMap_val,id_val,first_val,second_val,Part.bind_some,Part.map_some]
  p1_p1 X Y Z := by
    change productMap (second X Y) (𝟙 Z) ≫ second Y Z=second (product X Y) Z
    apply Arrow.ext
    funext p
    simp only [comp_val,productMap_val,id_val,first_val,second_val,Part.bind_some,Part.map_some]
  diag_nat f := by
    change f ≫ diagonal _=diagonal _ ≫ productMap f f
    rw [diagonal_productMap,diagonal,comp_pairing]
    simp only [Category.comp_id]
  p0_nat f := by
    change productMap f (𝟙 _) ≫ first _ _=first _ _ ≫ f
    apply Arrow.ext
    funext p
    simp only [comp_val,productMap_val,id_val,first_val,second_val,Part.bind_some,Part.map_some,Part.bind_assoc,Part.bind_map,Part.bind_some_right]
  p1_nat f := by
    change productMap (𝟙 _) f ≫ second _ _=second _ _ ≫ f
    apply Arrow.ext
    funext p
    simp only [comp_val,productMap_val,id_val,first_val,second_val,Part.bind_some,Part.map_some,Part.bind_assoc,Part.bind_map,Part.bind_some_right]
  assoc_nat f g h := by
    change productMap (productMap f g) h ≫ PCategoryStruct.assoc _ _ _=
      PCategoryStruct.assoc _ _ _ ≫ productMap f (productMap g h)
    apply Arrow.ext
    funext p
    simp only [comp_val,productMap_val,associator_val,Part.bind_some,Part.bind_assoc,
      Part.bind_map,Part.map_bind,Part.map_map,Function.comp_def,Part.bind_some_eq_map]
  swap_nat f g := by
    change productMap f g ≫ PCategoryStruct.swap _ _=PCategoryStruct.swap _ _ ≫ productMap g f
    apply hom_ext_mem
    intro p q
    simp only [comp_val,productMap_val,swap_val,Part.bind_some,Part.bind_map,Part.bind_assoc,
      Part.mem_bind_iff,Part.mem_map_iff,Part.mem_some_iff]
    constructor
    · rintro ⟨a,ha,b,hb,he⟩
      exact ⟨b,hb,a,ha,he.symm⟩
    · rintro ⟨b,hb,a,ha,he⟩
      exact ⟨a,ha,b,hb,he.symm⟩

theorem induced_restriction {X Y : Restricted S} (f : X ⟶ Y) :
    PCategoryStruct.rst f=rst (self := nativeRestriction) f := by
  change diagonal X ≫ productMap (𝟙 X) f ≫ first X Y=restriction f
  rw [← Category.assoc,diagonal_productMap]
  apply hom_ext_mem
  intro x y
  simp only [comp_val,pairing_val,first_val,id_val]
  change y ∈ (rawPair Part.some f.val x).bind (fun p => Part.some p.1) ↔
    y ∈ (identityOn X {x | (f.val x).Dom} f.domain).val x
  rw [mem_identityOn]
  simp only [rawPair,Part.bind_some,Part.mem_bind_iff,Part.mem_map_iff,Part.mem_some_iff]
  change (∃ a,(∃ b,b ∈ f.val x ∧ (x,b)=a) ∧ y=a.1) ↔ (f.val x).Dom ∧ y=x
  rw [Part.dom_iff_mem]
  aesop

instance prodominical : RecursionCategory.Prodominical (Restricted S) where
  nearProd_zero_right f := by
    apply hom_ext_mem
    intro p q
    change q ∈ (productMap f 0).val p ↔ q ∈ (Part.none : Part _)
    rw [mem_productMap]
    simp only [zero_val,Part.notMem_none,and_false]
  nearProd_zero_left f := by
    apply hom_ext_mem
    intro p q
    change q ∈ (productMap 0 f).val p ↔ q ∈ (Part.none : Part _)
    rw [mem_productMap]
    simp only [zero_val,Part.notMem_none,false_and]

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted
