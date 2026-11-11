/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.OracleRestrictedRanges

/-! # Actual cartesian restriction products of the formal numerical types -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted

variable {S : Set ℕ}

@[implicit_reducible] def product (X Y : Restricted S) : Restricted S := ⟨.product X.type Y.type⟩

def rawPair {α β γ : Type} (f : α → Part β) (g : α → Part γ) (x : α) : Part (β × γ) :=
  (f x).bind (fun y => (g x).map (Prod.mk y))

theorem mem_rawPair {α β γ : Type} (f : α → Part β) (g : α → Part γ)
    (x : α) (y : β) (z : γ) : (y,z) ∈ rawPair f g x ↔ y ∈ f x ∧ z ∈ g x := by
  simp only [rawPair,Part.mem_bind_iff,Part.mem_map_iff,Prod.mk.injEq]
  aesop

theorem rawPair_partrec {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]
    {f : α → Part β} {g : α → Part γ} (hf : Partrec f) (hg : Partrec g) : Partrec (rawPair f g) :=
  hf.bind (((hg.comp Computable.fst).map
    (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd).to₂).to₂)

theorem rawPair_dom {α β γ : Type} (f : α → Part β) (g : α → Part γ) (x : α) :
    (rawPair f g x).Dom ↔ (f x).Dom ∧ (g x).Dom := by
  simp only [Part.dom_iff_mem]
  constructor
  · rintro ⟨⟨y,z⟩,h⟩
    obtain ⟨hy,hz⟩ := (mem_rawPair f g x y z).mp h
    exact ⟨⟨y,hy⟩,⟨z,hz⟩⟩
  · rintro ⟨⟨y,hy⟩,⟨z,hz⟩⟩
    exact ⟨(y,z),(mem_rawPair f g x y z).mpr ⟨hy,hz⟩⟩

def pairing {W X Y : Restricted S} (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ product X Y := by
  refine ⟨rawPair f.val g.val,?_,?_⟩
  · exact (f.domain.and g.domain).of_eq (fun x => (rawPair_dom f.val g.val x).symm)
  · obtain ⟨f₀,hf,he⟩ := f.extension
    obtain ⟨g₀,hg,hge⟩ := g.extension
    refine ⟨rawPair f₀ g₀,rawPair_partrec hf hg,?_⟩
    rintro x ⟨y,z⟩ h
    obtain ⟨hy,hz⟩ := (mem_rawPair f.val g.val x y z).mp h
    exact (mem_rawPair f₀ g₀ x y z).mpr ⟨he x y hy,hge x z hz⟩

@[simp] theorem mem_pairing {W X Y : Restricted S} (f : W ⟶ X) (g : W ⟶ Y)
    (w : carrier S W) (x : carrier S X) (y : carrier S Y) :
    (x,y) ∈ (pairing f g).val w ↔ x ∈ f.val w ∧ y ∈ g.val w := mem_rawPair f.val g.val w x y

def first (X Y : Restricted S) : product X Y ⟶ X := totalFromFunction Prod.fst Computable.fst
def second (X Y : Restricted S) : product X Y ⟶ Y := totalFromFunction Prod.snd Computable.snd
def diagonal (X : Restricted S) : X ⟶ product X X := pairing (𝟙 X) (𝟙 X)

def productMap {W X Y Z : Restricted S} (f : W ⟶ X) (g : Y ⟶ Z) : product W Y ⟶ product X Z :=
  pairing (first W Y ≫ f) (second W Y ≫ g)

@[simp] theorem mem_comp {X Y Z : Restricted S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : carrier S X) (z : carrier S Z) :
    z ∈ (f ≫ g).val x ↔ ∃ y,y ∈ f.val x ∧ z ∈ g.val y := Part.mem_bind_iff

@[simp] theorem mem_first (X Y : Restricted S) (p : carrier S (product X Y)) (x : carrier S X) :
    x ∈ (first X Y).val p ↔ x=p.1 := Part.mem_some_iff

@[simp] theorem mem_second (X Y : Restricted S) (p : carrier S (product X Y)) (y : carrier S Y) :
    y ∈ (second X Y).val p ↔ y=p.2 := Part.mem_some_iff

@[simp] theorem mem_diagonal (X : Restricted S) (x : carrier S X) (p : carrier S (product X X)) :
    p ∈ (diagonal X).val x ↔ p=(x,x) := by
  rcases p with ⟨y,z⟩
  change (y,z) ∈ rawPair Part.some Part.some x ↔ (y,z)=(x,x)
  rw [mem_rawPair]
  simp only [Part.mem_some_iff,Prod.mk.injEq]

@[simp] theorem mem_productMap {W X Y Z : Restricted S} (f : W ⟶ X) (g : Y ⟶ Z)
    (p : carrier S (product W Y)) (q : carrier S (product X Z)) :
    q ∈ (productMap f g).val p ↔ q.1 ∈ f.val p.1 ∧ q.2 ∈ g.val p.2 := by
  rcases q with ⟨x,z⟩
  change (x,z) ∈ rawPair (first W Y ≫ f).val (second W Y ≫ g).val p ↔ _
  rw [mem_rawPair]
  change x ∈ (Part.some p.1).bind f.val ∧ z ∈ (Part.some p.2).bind g.val ↔ _
  simp only [Part.bind_some]

theorem comp_pairing {W X Y Z : Restricted S} (h : W ⟶ X) (f : X ⟶ Y) (g : X ⟶ Z) :
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

theorem productMap_comp {U V W X Y Z : Restricted S}
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

@[simp] theorem comp_val {X Y Z : Restricted S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val=fun x => (f.val x).bind g.val := rfl

@[simp] theorem id_val (X : Restricted S) : (𝟙 X : X ⟶ X).val=Part.some := rfl

@[simp] theorem pairing_val {W X Y : Restricted S} (f : W ⟶ X) (g : W ⟶ Y) :
    (pairing f g).val=rawPair f.val g.val := rfl

@[simp] theorem first_val (X Y : Restricted S) :
    (first X Y).val=fun p => Part.some p.1 := rfl

@[simp] theorem second_val (X Y : Restricted S) :
    (second X Y).val=fun p => Part.some p.2 := rfl

@[simp] theorem diagonal_val (X : Restricted S) :
    (diagonal X).val=fun x => Part.some (x,x) := by
  funext x
  simp only [diagonal,pairing_val,rawPair,id_val,Part.bind_some,Part.map_some]

@[simp] theorem productMap_val {W X Y Z : Restricted S} (f : W ⟶ X) (g : Y ⟶ Z) :
    (productMap f g).val=fun p => (f.val p.1).bind (fun x => (g.val p.2).map (Prod.mk x)) := by
  funext p
  simp only [productMap,pairing_val,rawPair,comp_val,first_val,second_val,Part.bind_some]

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted
