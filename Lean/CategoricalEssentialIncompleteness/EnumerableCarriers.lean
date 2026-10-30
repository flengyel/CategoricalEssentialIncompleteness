/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.ClassicalSplitMaps
import Mathlib.CategoryTheory.Widesubcategory

/-! # Computably enumerable numerical carriers and partial recursive maps -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms)

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

open ClassicalPrograms

structure Carrier where
  support : Set ℕ
  enumerable : REPred (· ∈ support)

def partialObject (X : Carrier) : SplitObject Rec := ceObject X.support X.enumerable

instance carrierCategory : Category Carrier where
  Hom X Y := partialObject X ⟶ partialObject Y
  id X := 𝟙 (partialObject X)
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

def inclusion : Carrier ⥤ SplitObject Rec where
  obj := partialObject
  map f := f

instance : inclusion.Faithful where
  map_injective h := h

instance : inclusion.Full where
  map_surjective f := ⟨f, rfl⟩

instance carrierRestriction : RestrictionCategory Carrier where
  rst f := rst (C := SplitObject Rec) f
  rst_comp_self f := rst_comp_self (C := SplitObject Rec) f
  rst_comm f g := rst_comm (C := SplitObject Rec) f g
  rst_comp_rst f g := rst_comp_rst (C := SplitObject Rec) f g
  rst_comp f g := rst_comp (C := SplitObject Rec) f g

instance : HasZeroMorphisms Carrier where
  zero X Y := inferInstanceAs (Zero (partialObject X ⟶ partialObject Y))
  comp_zero := by intros; exact CategoryTheory.Limits.comp_zero (C := SplitObject Rec)
  zero_comp := by intros; exact CategoryTheory.Limits.zero_comp (C := SplitObject Rec)

instance : RestrictionZero Carrier where
  restrict_zero X Y := RestrictionZero.restrict_zero (partialObject X) (partialObject Y)

def toSplitIdem {X : Carrier} (a : Idem X) : Idem (partialObject X) := ⟨a.hom, a.restriction⟩
def ofSplitIdem {X : Carrier} (a : Idem (partialObject X)) : Idem X := ⟨a.hom, a.restriction⟩

def idemOrderIso (X : Carrier) : Idem X ≃o Idem (partialObject X) where
  toFun := toSplitIdem
  invFun := ofSplitIdem
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

instance : Ranges Carrier where
  range f := ofSplitIdem (Ranges.range (C := SplitObject Rec) f)
  receives f := Ranges.receives (C := SplitObject Rec) f
  agreement f g h he := Ranges.agreement (C := SplitObject Rec) f g h he

instance : BinaryJoins Carrier where
  join a b := ofSplitIdem (toSplitIdem a ⊔ toSplitIdem b)
  le_left a b := (idemOrderIso _).symm.monotone
    (show toSplitIdem a ≤ toSplitIdem a ⊔ toSplitIdem b from le_sup_left)
  le_right a b := (idemOrderIso _).symm.monotone
    (show toSplitIdem b ≤ toSplitIdem a ⊔ toSplitIdem b from le_sup_right)
  least a b c ha hb := (idemOrderIso _).symm.monotone
    (sup_le ((idemOrderIso _).monotone ha) ((idemOrderIso _).monotone hb))

instance : JoinInverse Carrier where
  pull_sup f a b := Idem.ext (congrArg (fun e : Idem (partialObject _) => e.hom)
    (JoinInverse.pull_sup (C := SplitObject Rec) f (toSplitIdem a) (toSplitIdem b)))

def val {X Y : Carrier} (f : X ⟶ Y) : ℕ → Part ℕ := J.map f.hom

theorem val_injective {X Y : Carrier} : Function.Injective (val (X := X) (Y := Y)) := by
  intro f g h
  apply SplitObject.Hom.ext
  exact J.map_injective h

@[simp] theorem val_id (X : Carrier) : val (𝟙 X) = supportIdentity X.support := rfl
@[simp] theorem val_comp {X Y Z : Carrier} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    val (f ≫ g) n = (val f n).bind (val g) := rfl
@[simp] theorem val_zero (X Y : Carrier) : val (0 : X ⟶ Y) = fun _ => Part.none := rfl

theorem val_restriction {X Y : Carrier} (f : X ⟶ Y) :
    val (rst f) = PartialFunctions.restriction (X := PartialFun.of ℕ) (Y := PartialFun.of ℕ) (val f) :=
  J_rst f.hom

theorem val_partrec {X Y : Carrier} (f : X ⟶ Y) : Partrec (val f) := omegaArrow_partrec f.hom

theorem val_source {X Y : Carrier} (f : X ⟶ Y) (x y : ℕ) (h : y ∈ val f x) : x ∈ X.support := by
  have hh : y ∈ J.map ((partialObject X).domain.hom ≫ f.hom) x := by
    rw [f.source]
    exact h
  rw [J.map_comp] at hh
  obtain ⟨z, hz, _⟩ := (PartialFunctions.mem_comp _ _ x y).mp hh
  exact ((mem_supportIdentity X.support x z).mp hz).1

theorem val_target {X Y : Carrier} (f : X ⟶ Y) (x y : ℕ) (h : y ∈ val f x) : y ∈ Y.support := by
  have hh : y ∈ J.map (f.hom ≫ (partialObject Y).domain.hom) x := by
    rw [f.target]
    exact h
  rw [J.map_comp] at hh
  obtain ⟨z, _, hz⟩ := (PartialFunctions.mem_comp _ _ x y).mp hh
  obtain ⟨hY, he⟩ := (mem_supportIdentity Y.support z y).mp hz
  exact he ▸ hY

theorem total_iff {X Y : Carrier} (f : X ⟶ Y) :
    isTotal f ↔ ∀ x ∈ X.support, (val f x).Dom := by
  constructor
  · intro ht x hx
    have hh : x ∈ val (rst f) x := by
      rw [show rst f = 𝟙 X from ht, val_id]
      exact (mem_supportIdentity X.support x x).mpr ⟨hx, rfl⟩
    rw [val_restriction] at hh
    obtain ⟨z, hz⟩ := ((PartialFunctions.mem_restriction _ x x).mp hh).1
    exact hz.1
  · intro ht
    apply val_injective
    rw [val_restriction, val_id]
    apply PFun.ext
    intro x y
    rw [PartialFunctions.mem_restriction, mem_supportIdentity]
    constructor
    · rintro ⟨⟨z, hz⟩, he⟩
      exact ⟨val_source f x z hz, he⟩
    · rintro ⟨hx, he⟩
      exact ⟨⟨(val f x).get (ht x hx), Part.get_mem _⟩, he⟩

@[simp] theorem mem_val_comp {X Y Z : Carrier} (f : X ⟶ Y) (g : Y ⟶ Z) (x z : ℕ) :
    z ∈ val (f ≫ g) x ↔ ∃ y, y ∈ val f x ∧ z ∈ val g y := Part.mem_bind_iff

@[simp] theorem mem_val_restriction {X Y : Carrier} (f : X ⟶ Y) (x y : ℕ) :
    y ∈ val (rst f) x ↔ (∃ z, z ∈ val f x) ∧ y = x := by
  rw [val_restriction]
  exact PartialFunctions.mem_restriction _ x y

def support {X : Carrier} (a : Idem X) : Set ℕ := splitSupport (toSplitIdem a)

theorem mem_val_idem {X : Carrier} (a : Idem X) (x y : ℕ) :
    y ∈ val a.hom x ↔ x ∈ support a ∧ y = x :=
  PartialFunctions.mem_idem (inclusionRangeFunctor.mapIdem
    (SplitObject.baseIdem (toSplitIdem a))) x y

theorem support_injective {X : Carrier} : Function.Injective (support (X := X)) := by
  intro a b h
  exact (idemOrderIso X).injective (splitSupport_injective h)

theorem support_le_iff {X : Carrier} (a b : Idem X) :
    a ≤ b ↔ support a ⊆ support b := splitSupport_le_iff (toSplitIdem a) (toSplitIdem b)

@[simp] theorem support_inf {X : Carrier} (a b : Idem X) :
    support (a ⊓ b) = support a ∩ support b := splitSupport_inf (toSplitIdem a) (toSplitIdem b)

@[simp] theorem support_sup {X : Carrier} (a b : Idem X) :
    support (a ⊔ b) = support a ∪ support b := splitSupport_sup _ _

@[simp] theorem support_bot (X : Carrier) : support (⊥ : Idem X) = ∅ := splitSupport_bot

@[simp] theorem support_top (X : Carrier) : support (⊤ : Idem X) = X.support := by
  change PartialFunctions.support
    (inclusionRangeFunctor.mapIdem (supportIdem X.support X.enumerable)) = X.support
  rw [supportIdem_image, PartialFunctions.support_setIdem]

theorem support_subset {X : Carrier} (a : Idem X) : support a ⊆ X.support := by
  intro x hx
  exact val_source a.hom x x ((mem_val_idem a x x).mpr ⟨hx, rfl⟩)

theorem support_re {X : Carrier} (a : Idem X) : REPred (· ∈ support a) := by
  apply (val_partrec a.hom).dom_re.of_eq
  intro x
  rw [Part.dom_iff_mem]
  simp only [mem_val_idem, exists_eq_right]

theorem support_pull {X Y : Carrier} (f : X ⟶ Y) (a : Idem Y) :
    support (Idem.pull f a) = {x | ∃ y, y ∈ val f x ∧ y ∈ support a} :=
  splitSupport_pull f (toSplitIdem a)

@[simp] theorem support_range {X Y : Carrier} (f : X ⟶ Y) :
    support (Ranges.range f) = {y | ∃ x, y ∈ val f x} :=
  PartialFunctions.support_setIdem _

def relativeIdem {X : Carrier} (A : Set ℕ) (hA : REPred (· ∈ A)) (h : A ⊆ X.support) :
    Idem X := ofSplitIdem
  (SplitObject.relativeIdem (supportIdem A hA) (supportIdem_le hA X.enumerable h))

@[simp] theorem support_relativeIdem {X : Carrier}
    (A : Set ℕ) (hA : REPred (· ∈ A)) (h : A ⊆ X.support) :
    support (relativeIdem A hA h) = A := splitSupport_relative hA X.enumerable h

def arrow {X Y : Carrier} (f : ℕ → Part ℕ) (hf : Partrec f)
    (hs : ∀ x y, y ∈ f x → x ∈ X.support)
    (ht : ∀ x y, y ∈ f x → y ∈ Y.support) : X ⟶ Y :=
  supportedArrow X.enumerable Y.enumerable f hf hs ht

@[simp] theorem val_arrow {X Y : Carrier} (f : ℕ → Part ℕ) (hf : Partrec f)
    (hs : ∀ x y, y ∈ f x → x ∈ X.support)
    (ht : ∀ x y, y ∈ f x → y ∈ Y.support) : val (arrow f hf hs ht) = f := rfl

def singletonIdem {X : Carrier} (x : ℕ) (hx : x ∈ X.support) : Idem X :=
  relativeIdem {x} ((Primrec.eq.comp Primrec.id (Primrec.const x)).computablePred.to_re)
    (Set.singleton_subset_iff.mpr hx)

@[simp] theorem support_singletonIdem {X : Carrier} (x : ℕ) (hx : x ∈ X.support) :
    support (singletonIdem x hx) = {x} := support_relativeIdem _ _ _

theorem eq_at_of_precomp_idem {X Y : Carrier} (a : Idem X) (f g : X ⟶ Y)
    (he : a.hom ≫ f = a.hom ≫ g) (x : ℕ) (hx : x ∈ support a) : val f x = val g x := by
  have hi : val a.hom x = Part.some x :=
    Part.eq_some_iff.mpr ((mem_val_idem a x x).mpr ⟨hx, rfl⟩)
  have hh := congrArg (fun k => val k x) he
  simpa only [val_comp, hi, Part.bind_some] using hh

theorem val_ext_on_source {X Y : Carrier} (f g : X ⟶ Y)
    (h : ∀ x ∈ X.support, val f x = val g x) : f = g := by
  apply val_injective
  apply PFun.ext
  intro x y
  by_cases hx : x ∈ X.support
  · rw [h x hx]
  · exact ⟨fun hy => False.elim (hx (val_source f x y hy)),
      fun hy => False.elim (hx (val_source g x y hy))⟩

@[simp] theorem mem_val_precomp_idem {X Y : Carrier} (a : Idem X) (f : X ⟶ Y) (x y : ℕ) :
    y ∈ val (a.hom ≫ f) x ↔ x ∈ support a ∧ y ∈ val f x := by
  rw [mem_val_comp]
  simp only [mem_val_idem]
  aesop

def subcarrier {X : Carrier} (a : Idem X) : Carrier := ⟨support a, support_re a⟩

def into {X : Carrier} (a : Idem X) : subcarrier a ⟶ X :=
  arrow (val a.hom) (val_partrec a.hom)
    (fun x y h => ((mem_val_idem a x y).mp h).1)
    (val_target a.hom)

def outof {X : Carrier} (a : Idem X) : X ⟶ subcarrier a :=
  arrow (val a.hom) (val_partrec a.hom) (val_source a.hom)
    (by
      intro x y h
      obtain ⟨hx, he⟩ := (mem_val_idem a x y).mp h
      exact he ▸ hx)

theorem into_total {X : Carrier} (a : Idem X) : isTotal (into a) := by
  apply (total_iff _).mpr
  intro x hx
  exact Part.dom_iff_mem.mpr ⟨x, (mem_val_idem a x x).mpr ⟨hx, rfl⟩⟩

theorem into_outof {X : Carrier} (a : Idem X) : into a ≫ outof a = 𝟙 (subcarrier a) := by
  apply val_injective
  apply PFun.ext
  intro x y
  change y ∈ (val a.hom x).bind (val a.hom) ↔ y ∈ supportIdentity (support a) x
  simp only [Part.mem_bind_iff, mem_val_idem, mem_supportIdentity]
  aesop

theorem outof_into {X : Carrier} (a : Idem X) : outof a ≫ into a = a.hom := by
  apply val_injective
  change val (a.hom ≫ a.hom) = val a.hom
  rw [a.idem]

def restrictMap {X Y : Carrier} (f : X ⟶ Y) (a : Idem X) (b : Idem Y)
    (h : ∀ x y, x ∈ support a → y ∈ val f x → y ∈ support b) :
    subcarrier a ⟶ subcarrier b :=
  arrow (val (a.hom ≫ f)) (val_partrec _)
    (fun x y hh => ((mem_val_precomp_idem a f x y).mp hh).1)
    (fun x y hh => h x y ((mem_val_precomp_idem a f x y).mp hh).1
      ((mem_val_precomp_idem a f x y).mp hh).2)

@[simp] theorem mem_val_restrictMap {X Y : Carrier} (f : X ⟶ Y) (a : Idem X) (b : Idem Y)
    (h : ∀ x y, x ∈ support a → y ∈ val f x → y ∈ support b) (x y : ℕ) :
    y ∈ val (restrictMap f a b h) x ↔ x ∈ support a ∧ y ∈ val f x :=
  mem_val_precomp_idem a f x y

theorem restrictMap_total {X Y : Carrier} (f : X ⟶ Y) (hf : isTotal f)
    (a : Idem X) (b : Idem Y)
    (h : ∀ x y, x ∈ support a → y ∈ val f x → y ∈ support b) :
    isTotal (restrictMap f a b h) := by
  apply (total_iff _).mpr
  intro x hx
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp ((total_iff f).mp hf x (support_subset a hx))
  exact Part.dom_iff_mem.mpr ⟨y, (mem_val_restrictMap f a b h x y).mpr ⟨hx, hy⟩⟩

theorem mem_support_ofRestrict {X Y : Carrier} (f : X ⟶ Y) (x : ℕ) :
    x ∈ support (Idem.ofRestrict f) ↔ (val f x).Dom := by
  have h := mem_val_idem (Idem.ofRestrict f) x x
  change x ∈ val (rst f) x ↔ _ at h
  simpa only [mem_val_restriction, eq_self_iff_true, and_true, ← Part.dom_iff_mem] using h.symm

def onDomain {X Y : Carrier} (f : X ⟶ Y) : subcarrier (Idem.ofRestrict f) ⟶ Y :=
  arrow (val f) (val_partrec f)
    (fun x y h => (mem_support_ofRestrict f x).mpr h.1) (val_target f)

theorem onDomain_total {X Y : Carrier} (f : X ⟶ Y) : isTotal (onDomain f) :=
  (total_iff _).mpr (fun x hx => (mem_support_ofRestrict f x).mp hx)

abbrev Total := WideSubcategory (isTotal (C := Carrier))

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers
