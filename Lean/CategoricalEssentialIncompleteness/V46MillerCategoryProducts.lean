/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerCategory

/-! # Actual restriction products in the representation-independent category -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
variable {z : Family}
attribute [instance 2000] nativeRestriction

@[implicit_reducible] def product (X Y : Object z) : Object z := ⟨.product X.type Y.type⟩

def rawPair {α β γ : Type} (f : α → Part β) (g : α → Part γ) (x : α) : Part (β × γ) :=
  (f x).bind (fun y => (g x).map (Prod.mk y))

theorem mem_rawPair {α β γ : Type} (f : α → Part β) (g : α → Part γ)
    (x : α) (y : β) (v : γ) : (y,v) ∈ rawPair f g x ↔ y ∈ f x ∧ v ∈ g x :=
  OracleComputation.Restricted.mem_rawPair f g x y v

def pairing {W X Y : Object z} (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ product X Y :=
  ⟨rawPair f.val g.val,Represented.pair f.represented g.represented⟩

@[simp] theorem mem_pairing {W X Y : Object z} (f : W ⟶ X) (g : W ⟶ Y)
    (w : carrier z W) (x : carrier z X) (y : carrier z Y) :
    (x,y) ∈ (pairing f g).val w ↔ x ∈ f.val w ∧ y ∈ g.val w := mem_rawPair f.val g.val w x y

def first (X Y : Object z) : product X Y ⟶ X := totalFromFunction Prod.fst Computable.fst
def second (X Y : Object z) : product X Y ⟶ Y := totalFromFunction Prod.snd Computable.snd
def diagonal (X : Object z) : X ⟶ product X X := pairing (𝟙 X) (𝟙 X)

def productMap {W X Y Z : Object z} (f : W ⟶ X) (g : Y ⟶ Z) : product W Y ⟶ product X Z :=
  pairing (first W Y ≫ f) (second W Y ≫ g)

@[simp] theorem mem_comp {X Y Z : Object z} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : carrier z X) (z : carrier z Z) :
    z ∈ (f ≫ g).val x ↔ ∃ y,y ∈ f.val x ∧ z ∈ g.val y := Part.mem_bind_iff

@[simp] theorem mem_first (X Y : Object z) (p : carrier z (product X Y)) (x : carrier z X) :
    x ∈ (first X Y).val p ↔ x=p.1 := Part.mem_some_iff

@[simp] theorem mem_second (X Y : Object z) (p : carrier z (product X Y)) (y : carrier z Y) :
    y ∈ (second X Y).val p ↔ y=p.2 := Part.mem_some_iff

@[simp] theorem mem_diagonal (X : Object z) (x : carrier z X) (p : carrier z (product X X)) :
    p ∈ (diagonal X).val x ↔ p=(x,x) := by
  rcases p with ⟨y,z⟩
  change (y,z) ∈ rawPair Part.some Part.some x ↔ (y,z)=(x,x)
  rw [mem_rawPair]
  simp only [Part.mem_some_iff,Prod.mk.injEq]

@[simp] theorem mem_productMap {W X Y Z : Object z} (f : W ⟶ X) (g : Y ⟶ Z)
    (p : carrier z (product W Y)) (q : carrier z (product X Z)) :
    q ∈ (productMap f g).val p ↔ q.1 ∈ f.val p.1 ∧ q.2 ∈ g.val p.2 := by
  rcases q with ⟨x,z⟩
  change (x,z) ∈ rawPair (first W Y ≫ f).val (second W Y ≫ g).val p ↔ _
  rw [mem_rawPair]
  change x ∈ (Part.some p.1).bind f.val ∧ z ∈ (Part.some p.2).bind g.val ↔ _
  simp only [Part.bind_some]

theorem comp_pairing {W X Y Z : Object z} (h : W ⟶ X) (f : X ⟶ Y) (g : X ⟶ Z) :
    h ≫ pairing f g=pairing (h ≫ f) (h ≫ g) := by
  apply Arrow.ext
  funext w
  apply Part.ext
  rintro ⟨y,z⟩
  change (y,z) ∈ (h.val w).bind (rawPair f.val g.val) ↔
    (y,z) ∈ rawPair (fun w => (h.val w).bind f.val) (fun w => (h.val w).bind g.val) w
  rw [mem_rawPair]
  simp only [Part.mem_bind_iff,mem_rawPair]
  constructor
  · rintro ⟨x,hx,hy,hz⟩
    exact ⟨⟨x,hx,hy⟩,⟨x,hx,hz⟩⟩
  · rintro ⟨⟨x,hx,hy⟩,⟨x',hx',hz⟩⟩
    have he : x'=x := Part.mem_unique hx' hx
    subst x'
    exact ⟨x,hx,hy,hz⟩

theorem productMap_comp {U V W X Y Z : Object z}
    (f : U ⟶ V) (g : V ⟶ W) (h : X ⟶ Y) (k : Y ⟶ Z) :
    productMap f h ≫ productMap g k=productMap (f ≫ g) (h ≫ k) := by
  apply Arrow.ext
  funext p
  apply Part.ext
  intro q
  simp only [mem_comp,mem_productMap]
  constructor
  · rintro ⟨⟨a,b⟩,⟨hf,hh⟩,hg,hk⟩
    exact ⟨⟨a,hf,hg⟩,⟨b,hh,hk⟩⟩
  · rintro ⟨⟨a,hf,hg⟩,⟨b,hh,hk⟩⟩
    exact ⟨(a,b),⟨hf,hh⟩,hg,hk⟩

@[simp] theorem pairing_val {W X Y : Object z} (f : W ⟶ X) (g : W ⟶ Y) :
    (pairing f g).val=rawPair f.val g.val := rfl

@[simp] theorem first_val (X Y : Object z) :
    (first X Y).val=fun p => Part.some p.1 := rfl

@[simp] theorem second_val (X Y : Object z) :
    (second X Y).val=fun p => Part.some p.2 := rfl

@[simp] theorem diagonal_val (X : Object z) :
    (diagonal X).val=fun x => Part.some (x,x) := by
  funext x
  simp only [diagonal,pairing_val,rawPair,id_val,Part.bind_some,Part.map_some]

@[simp] theorem productMap_val {W X Y Z : Object z} (f : W ⟶ X) (g : Y ⟶ Z) :
    (productMap f g).val=fun p => (f.val p.1).bind (fun x => (g.val p.2).map (Prod.mk x)) := by
  funext p
  simp only [productMap,pairing_val,rawPair,comp_val,first_val,second_val,Part.bind_some]


@[simp] theorem mem_id (X : Object z) (x y : carrier z X) :
    y ∈ (𝟙 X : X ⟶ X).val x ↔ y=x := Part.mem_some_iff

theorem productMap_id (X Y : Object z) : productMap (𝟙 X) (𝟙 Y)=𝟙 (product X Y) := by
  apply hom_ext_mem
  intro p q
  simp only [mem_productMap,mem_id]
  change (q.1=p.1 ∧ q.2=p.2) ↔ q=p
  exact Prod.ext_iff.symm

theorem diagonal_first (X : Object z) : diagonal X ≫ first X X=𝟙 X := by
  apply hom_ext_mem
  intro x y
  simp only [mem_comp,mem_diagonal,mem_first,mem_id,exists_eq_left]

theorem diagonal_second (X : Object z) : diagonal X ≫ second X X=𝟙 X := by
  apply hom_ext_mem
  intro x y
  simp only [mem_comp,mem_diagonal,mem_second,mem_id,exists_eq_left]

theorem diagonal_productMap {W X Y : Object z} (f : W ⟶ X) (g : W ⟶ Y) :
    diagonal W ≫ productMap f g=pairing f g := by
  apply hom_ext_mem
  intro w q
  rcases q with ⟨x,y⟩
  simp only [comp_val,diagonal_val,productMap_val,pairing_val,Part.bind_some,rawPair]

instance pcategoryStruct : PCategoryStruct (Object z) where
  nearProd := product
  nearProd_map := productMap
  diag := diagonal
  p0 := first
  p1 := second

@[simp] theorem p0_eq_first (X Y : Object z) : PCategoryStruct.p0 X Y=first X Y := rfl
@[simp] theorem p1_eq_second (X Y : Object z) : PCategoryStruct.p1 X Y=second X Y := rfl

theorem pcategory_pairing_eq {W X Y : Object z} (f : W ⟶ X) (g : W ⟶ Y) :
    PCategoryStruct.partialPairing f g=pairing f g := diagonal_productMap f g

theorem associator_val (X Y Z : Object z) :
    (PCategoryStruct.assoc X Y Z).val=fun p => Part.some (p.1.1,(p.1.2,p.2)) := by
  rw [PCategoryStruct.assoc,pcategory_pairing_eq,pcategory_pairing_eq]
  funext p
  simp only [pairing_val,rawPair,comp_val,p0_eq_first,p1_eq_second,first_val,second_val,Part.bind_some,Part.map_some]

theorem swap_val (X Y : Object z) :
    (PCategoryStruct.swap X Y).val=fun p => Part.some (p.2,p.1) := by
  rw [PCategoryStruct.swap,pcategory_pairing_eq]
  funext p
  simp only [pairing_val,rawPair,p0_eq_first,p1_eq_second,first_val,second_val,Part.bind_some,Part.map_some]

theorem mem_associator (X Y Z : Object z)
    (p : carrier z (product (product X Y) Z)) (q : carrier z (product X (product Y Z))) :
    q ∈ (PCategoryStruct.assoc X Y Z).val p ↔ q=(p.1.1,(p.1.2,p.2)) := by
  rw [associator_val]
  exact Part.mem_some_iff

theorem mem_swap (X Y : Object z) (p : carrier z (product X Y)) (q : carrier z (product Y X)) :
    q ∈ (PCategoryStruct.swap X Y).val p ↔ q=(p.2,p.1) := by
  rw [swap_val]
  exact Part.mem_some_iff

instance pcategory : PCategory (Object z) where
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
    simp only [comp_val,productMap_val,id_val,first_val,Part.bind_some,Part.map_some]
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
    simp only [comp_val,productMap_val,id_val,second_val,Part.bind_some,Part.map_some]
  diag_nat f := by
    change f ≫ diagonal _=diagonal _ ≫ productMap f f
    rw [diagonal_productMap,diagonal,comp_pairing]
    simp only [Category.comp_id]
  p0_nat f := by
    change productMap f (𝟙 _) ≫ first _ _=first _ _ ≫ f
    apply Arrow.ext
    funext p
    simp only [comp_val,productMap_val,id_val,first_val,Part.bind_some,Part.map_some,Part.bind_assoc,Part.bind_some_right]
  p1_nat f := by
    change productMap (𝟙 _) f ≫ second _ _=second _ _ ≫ f
    apply Arrow.ext
    funext p
    simp only [comp_val,productMap_val,id_val,second_val,Part.bind_some,Part.bind_map,Part.bind_some_right]
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

theorem induced_restriction {X Y : Object z} (f : X ⟶ Y) :
    PCategoryStruct.rst f=rst (self := nativeRestriction) f := by
  change diagonal X ≫ productMap (𝟙 X) f ≫ first X Y=restriction f
  rw [← Category.assoc,diagonal_productMap]
  apply hom_ext_mem
  intro x y
  simp only [comp_val,pairing_val,first_val,id_val]
  change y ∈ (rawPair Part.some f.val x).bind (fun p => Part.some p.1) ↔
    y ∈ (identityOn X {x | (f.val x).Dom} f.represented.domain).val x
  rw [mem_identityOn]
  simp only [rawPair,Part.bind_some,Part.mem_bind_iff,Part.mem_map_iff,Part.mem_some_iff]
  change (∃ a,(∃ b,b ∈ f.val x ∧ (x,b)=a) ∧ y=a.1) ↔ (f.val x).Dom ∧ y=x
  rw [Part.dom_iff_mem]
  aesop

instance prodominical : RecursionCategory.Prodominical (Object z) where
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


end CategoricalEssentialIncompleteness.V46.Miller.Uniform
