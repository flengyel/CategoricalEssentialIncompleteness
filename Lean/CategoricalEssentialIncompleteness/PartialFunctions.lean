/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.RestrictionCompatibility
import Mathlib.CategoryTheory.Category.PartialFun
import Mathlib.Tactic.Tauto

/-! # The category of sets and arbitrary partial functions

The morphisms are `Part`-valued functions, so their domains need not be
decidable. Restrictions and ranges are the partial identities on domains
and images, respectively.
-/

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms zero_comp comp_zero)
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions

abbrev Pfn := PartialFun.{u}

def partialIdentity (X : Pfn) (s : Set X) : X ⟶ X := PFun.res id s

@[simp] theorem mem_identity {X : Pfn} (s : Set X) (x y : X) :
    y ∈ partialIdentity X s x ↔ x ∈ s ∧ y = x := by
  simp only [partialIdentity, PFun.mem_res, id_eq, eq_comm]

@[simp] theorem mem_comp {X Y Z : Pfn} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (z : Z) :
    z ∈ (f ≫ g) x ↔ ∃ y, y ∈ f x ∧ z ∈ g y := Part.mem_bind_iff

@[simp] theorem mem_id {X : Pfn} (x y : X) : y ∈ (𝟙 X : X ⟶ X) x ↔ y = x :=
  Part.mem_some_iff

theorem mem_conjugate {X Y Z W : Pfn} (e : X ≃ Y) (d : Z ≃ W) (f : Y ⟶ W)
    (x : X) (z : Z) :
    z ∈ ((PartialFun.Iso.mk e).hom ≫ f ≫ (PartialFun.Iso.mk d).inv) x ↔
      d z ∈ f (e x) := by
  change z ∈ (Part.some (e x)).bind (fun y =>
    (f y).bind (fun w => Part.some (d.symm w))) ↔ _
  simp only [Part.bind_some, Part.mem_bind_iff, Part.mem_some_iff]
  constructor
  · rintro ⟨w, hw, he⟩
    have hed : d z = w := by rw [he, Equiv.apply_symm_apply]
    rwa [hed]
  · intro h
    exact ⟨d z, h, (d.symm_apply_apply z).symm⟩

def restriction {X Y : Pfn} (f : X ⟶ Y) : X ⟶ X := partialIdentity X f.Dom

@[simp] theorem mem_restriction {X Y : Pfn} (f : X ⟶ Y) (x y : X) :
    y ∈ restriction f x ↔ (∃ z, z ∈ f x) ∧ y = x := by
  simp only [restriction, mem_identity, PFun.mem_dom]

instance : RestrictionCategory Pfn where
  rst := restriction
  rst_comp_self f := by
    apply PFun.ext
    intro x y
    simp only [mem_comp, mem_restriction]
    constructor
    · rintro ⟨_, ⟨_, rfl⟩, hy⟩; exact hy
    · intro hy; exact ⟨x, ⟨⟨y, hy⟩, rfl⟩, hy⟩
  rst_comm f g := by
    apply PFun.ext
    intro x y
    simp only [mem_comp, mem_restriction]
    aesop
  rst_comp_rst f g := by
    apply PFun.ext
    intro x y
    simp only [mem_comp, mem_restriction]
    aesop
  rst_comp f g := by
    apply PFun.ext
    intro x y
    simp only [mem_comp, mem_restriction]
    constructor
    · rintro ⟨_, ⟨⟨z, w, hw, hz⟩, rfl⟩, hy⟩
      have hwy : w = y := Part.mem_unique hw hy
      subst w
      exact ⟨y, hy, ⟨z, hz⟩, rfl⟩
    · rintro ⟨_, hy, ⟨z, hz⟩, rfl⟩
      exact ⟨x, ⟨⟨z, y, hy, hz⟩, rfl⟩, hy⟩

@[simp] theorem mem_rst {X Y : Pfn} (f : X ⟶ Y) (x y : X) :
    y ∈ rst f x ↔ (∃ z, z ∈ f x) ∧ y = x := mem_restriction f x y

instance : HasZeroMorphisms Pfn where
  zero _ _ := ⟨fun _ => Part.none⟩
  comp_zero := by
    intro X Y f Z
    apply PFun.ext
    intro x z
    change z ∈ (f x).bind (fun _ => Part.none) ↔ z ∈ (Part.none : Part Z)
    simp
  zero_comp := by
    intro X Y Z f
    apply PFun.ext
    intro x z
    change z ∈ (Part.none : Part Y).bind f ↔ z ∈ (Part.none : Part Z)
    simp

@[simp] theorem mem_zero {X Y : Pfn} (x : X) (y : Y) :
    y ∈ (0 : X ⟶ Y) x ↔ False := iff_false_intro (Part.notMem_none y)

instance : RestrictionZero Pfn where
  restrict_zero X Y := by apply PFun.ext; intro x y; simp

def setIdem {X : Pfn} (s : Set X) : Idem X :=
  ⟨partialIdentity X s, by apply PFun.ext; intro x y; simp⟩

def support {X : Pfn} (a : Idem X) : Set X := a.hom.Dom

theorem mem_support {X : Pfn} (a : Idem X) (x : X) :
    x ∈ support a ↔ ∃ y, y ∈ a.hom x := PFun.mem_dom a.hom x

@[simp] theorem mem_idem {X : Pfn} (a : Idem X) (x y : X) :
    y ∈ a.hom x ↔ x ∈ support a ∧ y = x := by
  calc
    _ ↔ y ∈ rst a.hom x := by rw [a.restriction]
    _ ↔ (∃ z, z ∈ a.hom x) ∧ y = x := mem_rst a.hom x y
    _ ↔ _ := and_congr (mem_support a x).symm Iff.rfl

@[simp] theorem support_setIdem {X : Pfn} (s : Set X) : support (setIdem s) = s := by
  ext x
  simp only [mem_support, setIdem, mem_identity, exists_eq_right]

theorem setIdem_support {X : Pfn} (a : Idem X) : setIdem (support a) = a := by
  apply Idem.ext
  apply PFun.ext
  intro x y
  exact (mem_identity (support a) x y).trans (mem_idem a x y).symm

theorem support_injective {X : Pfn} : Function.Injective (support (X := X)) := by
  intro a b h
  rw [← setIdem_support a, h, setIdem_support b]

theorem le_iff_support {X : Pfn} (a b : Idem X) : a ≤ b ↔ support a ⊆ support b := by
  constructor
  · intro h x hx
    have hm : x ∈ (a.hom ≫ b.hom) x := by
      rw [Idem.le_def.mp h]
      exact (mem_idem a x x).mpr ⟨hx, rfl⟩
    obtain ⟨y, hy, hb⟩ := (mem_comp _ _ _ _).mp hm
    obtain ⟨_, he⟩ := (mem_idem a x y).mp hy
    subst y
    exact ((mem_idem b x x).mp hb).1
  · intro h
    apply Idem.le_def.mpr
    apply PFun.ext
    intro x y
    simp only [mem_comp, mem_idem]
    constructor
    · aesop
    · intro ha
      exact ⟨x, ⟨ha.1, rfl⟩, h ha.1, ha.2⟩

instance : Ranges Pfn where
  range f := setIdem {y | ∃ x, y ∈ f x}
  receives f := by
    apply PFun.ext
    intro x y
    simp only [mem_comp, setIdem, mem_identity, Set.mem_ofPred_eq]
    aesop
  agreement f g h heq := by
    have agree (y) (hy : ∃ x, y ∈ f x) : g y = h y := by
      obtain ⟨x, hx⟩ := hy
      have hp : f x = Part.some y := Part.eq_some_iff.mpr hx
      have hh := congrFun heq x
      change (f x).bind g = (f x).bind h at hh
      simpa only [hp, Part.bind_some] using hh
    apply PFun.ext
    intro y z
    simp only [mem_comp, setIdem, mem_identity, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨w, ⟨hw, hwy⟩, hg⟩
      subst w
      exact ⟨y, ⟨hw, rfl⟩, agree y hw ▸ hg⟩
    · rintro ⟨w, ⟨hw, hwy⟩, hg⟩
      subst w
      exact ⟨y, ⟨hw, rfl⟩, (agree y hw).symm ▸ hg⟩

@[simp] theorem mem_range {X Y : Pfn} (f : X ⟶ Y) (y z : Y) :
    z ∈ (Ranges.range f).hom y ↔ (∃ x, y ∈ f x) ∧ z = y := mem_identity _ y z

instance : BinaryJoins Pfn where
  join a b := setIdem (support a ∪ support b)
  le_left a b := (le_iff_support _ _).mpr (by rw [support_setIdem]; exact Set.subset_union_left)
  le_right a b := (le_iff_support _ _).mpr (by rw [support_setIdem]; exact Set.subset_union_right)
  least a b c ha hb := (le_iff_support _ _).mpr (by
    rw [support_setIdem]
    exact Set.union_subset ((le_iff_support _ _).mp ha) ((le_iff_support _ _).mp hb))

@[simp] theorem support_sup {X : Pfn} (a b : Idem X) :
    support (a ⊔ b) = support a ∪ support b := support_setIdem _

@[simp] theorem support_inf {X : Pfn} (a b : Idem X) :
    support (a ⊓ b) = support a ∩ support b := by
  ext x
  rw [mem_support]
  change (∃ y, y ∈ (a.hom ≫ b.hom) x) ↔ _
  simp only [mem_comp, mem_idem, Set.mem_inter_iff]
  aesop

@[simp] theorem support_bot {X : Pfn} : support (⊥ : Idem X) = ∅ := by
  ext x; simp [mem_support]

@[simp] theorem support_top {X : Pfn} : support (⊤ : Idem X) = Set.univ := by
  ext x; simp [mem_support]

@[simp] theorem support_pull {X Y : Pfn} (f : X ⟶ Y) (a : Idem Y) :
    support (Idem.pull f a) = {x | ∃ y, y ∈ f x ∧ y ∈ support a} := by
  ext x
  rw [mem_support]
  change (∃ z, z ∈ rst (f ≫ a.hom) x) ↔ _
  simp only [mem_rst, mem_comp, mem_idem, Set.mem_ofPred_eq]
  aesop

instance : JoinInverse Pfn where
  pull_sup f a b := by
    apply support_injective
    ext x
    simp only [support_pull, support_sup, Set.mem_union, Set.mem_ofPred_eq]
    aesop

def sumMap {W X Y Z : Pfn} (f : W ⟶ X) (g : Y ⟶ Z) :
    PartialFun.of (W ⊕ Y) ⟶ PartialFun.of (X ⊕ Z) :=
  Sum.elim (fun x => (f x).map Sum.inl) (fun y => (g y).map Sum.inr)

instance : CoprodStruct Pfn.{u} where
  coprod X Y := PartialFun.of (X ⊕ Y)
  coprod_map := sumMap
  codiag _ := fun s => Part.some (s.elim id id)
  i0 _ _ := fun x => Part.some (Sum.inl x)
  i1 _ _ := fun y => Part.some (Sum.inr y)

@[simp] theorem sum_map_inl {W X Y Z : Pfn} (f : W ⟶ X) (g : Y ⟶ Z) (x : W) :
    coprod_map f g (Sum.inl x) = (f x).map Sum.inl := rfl

@[simp] theorem sum_map_inr {W X Y Z : Pfn} (f : W ⟶ X) (g : Y ⟶ Z) (y : Y) :
    coprod_map f g (Sum.inr y) = (g y).map Sum.inr := rfl

@[simp] theorem i0_apply {X Y : Pfn} (x : X) : i0 X Y x = Part.some (Sum.inl x) := rfl
@[simp] theorem i1_apply {X Y : Pfn} (y : Y) : i1 X Y y = Part.some (Sum.inr y) := rfl
@[simp] theorem codiag_apply {X : Pfn} (s : X ⊕ X) :
    codiag X s = Part.some (s.elim id id) := rfl

instance : CategoryTheory.HasCoproducts Pfn where
  coprod_id X Y := by
    apply PFun.ext
    intro s z
    cases s <;> simp [Part.mem_map_iff, eq_comm]
  coprod_comp f g h k := by
    apply PFun.ext
    intro s z
    cases s <;> simp only [mem_comp, sum_map_inl, sum_map_inr, Part.mem_map_iff] <;> aesop
  i0_codiag X := by apply PFun.ext; intro x z; simp
  i1_codiag X := by apply PFun.ext; intro x z; simp
  i0_i1_codiag X Y := by
    apply PFun.ext
    intro s z
    cases s <;> simp
  codiag_nat f := by
    apply PFun.ext
    intro s z
    cases s <;> simp [Part.mem_map_iff]
  i0_nat f := by apply PFun.ext; intro x z; simp [Part.mem_map_iff]; aesop
  i0_nat_right g := by apply PFun.ext; intro x z; simp [eq_comm]
  i1_nat f := by apply PFun.ext; intro x z; simp [Part.mem_map_iff]; aesop
  i1_nat_left f := by apply PFun.ext; intro x z; simp [eq_comm]

@[simp] theorem copair_inl {X Y Z : Pfn} (f : X ⟶ Z) (g : Y ⟶ Z) (x : X) :
    CategoryTheory.CoprodStruct.copair f g (Sum.inl x) = f x := by
  have h := congrFun (CategoryTheory.HasCoproducts.i0_copair f g) x
  change (Part.some (Sum.inl x)).bind (copair f g) = f x at h
  simpa only [Part.bind_some] using h

@[simp] theorem copair_inr {X Y Z : Pfn} (f : X ⟶ Z) (g : Y ⟶ Z) (y : Y) :
    CategoryTheory.CoprodStruct.copair f g (Sum.inr y) = g y := by
  have h := congrFun (CategoryTheory.HasCoproducts.i1_copair f g) y
  change (Part.some (Sum.inr y)).bind (copair f g) = g y at h
  simpa only [Part.bind_some] using h

instance : Splits Pfn where
  splitting a := by
    let Z : Pfn := PartialFun.of {x // x ∈ support a}
    let m : Z ⟶ _ := fun x => Part.some x.val
    let r : _ ⟶ Z := PFun.toSubtype (fun x => x ∈ support a) id
    have hr (x) (z : Z) : z ∈ r x ↔ z.val = x := PFun.mem_toSubtype_iff
    refine ⟨Z, m, r, ?_, ?_, ?_⟩
    · apply PFun.ext
      intro x y
      simp [m]
    · apply PFun.ext
      intro x y
      simp only [mem_comp, m, Part.mem_some_iff, hr, exists_eq_left, mem_id]
      exact Subtype.coe_inj
    · apply PFun.ext
      intro x y
      simp only [mem_comp, hr, m, Part.mem_some_iff,
        mem_idem]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz ▸ z.property, hz⟩
      · rintro ⟨hx, hy⟩
        exact ⟨⟨x, hx⟩, rfl, hy⟩

theorem singleton_connected {X : Pfn} (x : X) : Connected (setIdem {x}) := by
  intro b c he hd
  classical
  by_cases hb : b = ⊥
  · exact Or.inl hb
  right
  apply support_injective
  rw [support_bot]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hb' : (support b).Nonempty := Set.nonempty_iff_ne_empty.mpr (by
    intro hempty
    apply hb
    apply support_injective
    rw [support_bot, hempty])
  obtain ⟨y, hy⟩ := hb'
  have he' := congrArg support he
  rw [support_setIdem, support_sup] at he'
  have hyx : y = x := by
    have h : y ∈ ({x} : Set X) := by rw [he']; exact Or.inl hy
    exact h
  have hzx : z = x := by
    have h : z ∈ ({x} : Set X) := by rw [he']; exact Or.inr hz
    exact h
  have hd' := congrArg support hd
  rw [support_inf, support_bot] at hd'
  have hmem : x ∈ support b ∩ support c := ⟨hyx ▸ hy, hzx ▸ hz⟩
  rw [hd'] at hmem
  exact hmem

instance : LocallyConnected Pfn where
  hom_ext f g h := by
    funext x
    have he := congrFun (h (setIdem {x}) (singleton_connected x)) x
    change (partialIdentity _ {x} x).bind f = (partialIdentity _ {x} x).bind g at he
    have hx : partialIdentity _ {x} x = Part.some x :=
      Part.eq_some_iff.mpr ((mem_identity _ x x).mpr ⟨rfl, rfl⟩)
    simpa only [hx, Part.bind_some] using he

/-- A chosen preimage, defined on exactly the image of the original map. -/
noncomputable def chosenSection {X Y : Pfn} (f : X ⟶ Y) : Y ⟶ X :=
  fun y => ⟨∃ x, y ∈ f x, fun h => Classical.choose h⟩

theorem chosenSection_sound {X Y : Pfn} (f : X ⟶ Y) (y : Y) (x : X)
    (h : x ∈ chosenSection f y) : y ∈ f x := by
  obtain ⟨hdom, hx⟩ := Part.mem_mk_iff.mp h
  have hs := Classical.choose_spec hdom
  rwa [hx] at hs

theorem chosenSection_domain {X Y : Pfn} (f : X ⟶ Y) (y : Y) :
    (∃ x, x ∈ chosenSection f y) ↔ ∃ x, y ∈ f x :=
  (show (chosenSection f y).Dom ↔ ∃ x, x ∈ chosenSection f y from Part.dom_iff_mem).symm

theorem chosenSection_isSection {X Y : Pfn} (f : X ⟶ Y) :
    SectionOf f (chosenSection f) := by
  have hcomp : chosenSection f ≫ f = rst (chosenSection f) := by
    apply PFun.ext
    intro y z
    simp only [mem_comp, mem_rst]
    constructor
    · rintro ⟨x, hx, hz⟩
      exact ⟨⟨x, hx⟩, Part.mem_unique hz (chosenSection_sound f y x hx)⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, hx, chosenSection_sound f _ x hx⟩
  refine ⟨hcomp, ?_⟩
  rw [hcomp]
  apply PFun.ext
  intro x y
  simp only [mem_comp, mem_rst, chosenSection_domain]
  aesop

instance : WeakChoice Pfn where
  section_exists f _ := ⟨chosenSection f, chosenSection_isSection f⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
