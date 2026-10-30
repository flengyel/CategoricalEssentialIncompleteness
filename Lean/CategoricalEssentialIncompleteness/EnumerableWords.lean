/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnumerableProducts
import CategoricalEssentialIncompleteness.PartialListMap
import CategoricalEssentialIncompleteness.NonemptyWordCoding

/-! # Nonempty words in c.e. carriers -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness

namespace PartialLists

theorem traverse_total {f : ℕ → Part ℕ} (xs : List ℕ)
    (h : ∀ x ∈ xs,(f x).Dom) : (traverse f xs).Dom := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp (h x List.mem_cons_self)
    obtain ⟨ys,hys⟩ := Part.dom_iff_mem.mp (ih (fun z hz => h z (List.mem_cons_of_mem x hz)))
    exact Part.dom_iff_mem.mpr ⟨y::ys,(mem_traverse f _ _).mpr
      (List.Forall₂.cons hy ((mem_traverse f xs ys).mp hys))⟩

theorem forall₂_source {X Y : EnumerableCarriers.Carrier} (f : X ⟶ Y)
    {xs ys : List ℕ} (h : List.Forall₂ (fun x y => y ∈ EnumerableCarriers.val f x) xs ys) :
    ∀ x ∈ xs,x ∈ X.support := by
  induction h with
  | nil => simp
  | @cons x y xs ys hxy hxs ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl|hz
    · exact EnumerableCarriers.val_source f _ _ hxy
    · exact ih z hz

theorem forall₂_target {X Y : EnumerableCarriers.Carrier} (f : X ⟶ Y)
    {xs ys : List ℕ} (h : List.Forall₂ (fun x y => y ∈ EnumerableCarriers.val f x) xs ys) :
    ∀ y ∈ ys,y ∈ Y.support := by
  induction h with
  | nil => simp
  | @cons x y xs ys hxy hxs ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl|hz
    · exact EnumerableCarriers.val_target f _ _ hxy
    · exact ih z hz

theorem identity_dom (X : EnumerableCarriers.Carrier) (xs : List ℕ) :
    (traverse (EnumerableCarriers.val (𝟙 X)) xs).Dom ↔ ∀ x ∈ xs,x ∈ X.support := by
  constructor
  · intro h
    obtain ⟨ys,hys⟩ := Part.dom_iff_mem.mp h
    exact forall₂_source (𝟙 X) ((mem_traverse _ _ _).mp hys)
  · intro h
    apply traverse_total
    intro x hx
    exact Part.dom_iff_mem.mpr ⟨x,(mem_supportIdentity X.support x x).mpr ⟨h x hx,rfl⟩⟩

theorem identity_graph (X : EnumerableCarriers.Carrier) (xs ys : List ℕ) :
    List.Forall₂ (fun x y => y ∈ EnumerableCarriers.val (𝟙 X) x) xs ys ↔
      ys=xs ∧ ∀ x ∈ xs,x ∈ X.support := by
  induction xs generalizing ys with
  | nil => simp [List.forall₂_nil_left_iff]
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      rw [List.forall₂_cons,ih]
      simp only [EnumerableCarriers.val_id,mem_supportIdentity,
        List.cons.injEq,List.forall_mem_cons]
      tauto

theorem composition_graph {X Y Z : EnumerableCarriers.Carrier} (f : X ⟶ Y) (g : Y ⟶ Z)
    (xs zs : List ℕ) :
    List.Forall₂ (fun x z => z ∈ EnumerableCarriers.val (f ≫ g) x) xs zs ↔
      ∃ ys,List.Forall₂ (fun x y => y ∈ EnumerableCarriers.val f x) xs ys ∧
        List.Forall₂ (fun y z => z ∈ EnumerableCarriers.val g y) ys zs := by
  induction xs generalizing zs with
  | nil => simp [List.forall₂_nil_left_iff]
  | cons x xs ih =>
    cases zs with
    | nil => simp
    | cons z zs =>
      rw [List.forall₂_cons,ih]
      simp only [EnumerableCarriers.mem_val_comp]
      constructor
      · rintro ⟨⟨y,hxy,hyz⟩,ys,hxs,hys⟩
        exact ⟨y::ys,List.Forall₂.cons hxy hxs,List.Forall₂.cons hyz hys⟩
      · rintro ⟨ys,hxs,hys⟩
        cases hxs with
        | cons hxy hxs =>
          cases hys with
          | cons hyz hys => exact ⟨⟨_,hxy,hyz⟩,_,hxs,hys⟩

end PartialLists

namespace EnumerableCarriers

def words (X : Carrier) : Carrier where
  support := {n | (PartialLists.traverse (val (𝟙 X)) (WordCoding.decode n)).Dom}
  enumerable := ((PartialLists.traverse_partrec (val_partrec (𝟙 X))).comp
    WordCoding.decode_computable).dom_re

theorem mem_words (X : Carrier) (n : ℕ) :
    n ∈ (words X).support ↔ ∀ x ∈ WordCoding.decode n,x ∈ X.support :=
  PartialLists.identity_dom X _

def wordRaw {X Y : Carrier} (f : X ⟶ Y) (n : ℕ) : Part ℕ :=
  (PartialLists.traverse (val f) (WordCoding.decode n)).map WordCoding.encode

theorem wordRaw_partrec {X Y : Carrier} (f : X ⟶ Y) : Partrec (wordRaw f) :=
  ((PartialLists.traverse_partrec (val_partrec f)).comp WordCoding.decode_computable).map
    (WordCoding.encode_computable.comp Computable.snd).to₂

theorem wordRaw_graph {X Y : Carrier} (f : X ⟶ Y) (n m : ℕ) :
    m ∈ wordRaw f n ↔ List.Forall₂ (fun x y => y ∈ val f x)
      (WordCoding.decode n) (WordCoding.decode m) := by
  constructor
  · intro hm
    obtain ⟨ys,hys,he⟩ := (Part.mem_map_iff _).mp hm
    have h := (PartialLists.mem_traverse _ _ _).mp hys
    have hyne : ys≠[] := by
      intro hy
      have hl := h.length_eq
      rw [hy,List.length_nil] at hl
      exact WordCoding.decode_ne_nil n (List.length_eq_zero_iff.mp hl)
    rw [← he,WordCoding.decode_encode ys hyne]
    exact h
  · intro h
    exact (Part.mem_map_iff _).mpr ⟨WordCoding.decode m,
      (PartialLists.mem_traverse _ _ _).mpr h,WordCoding.encode_decode m⟩

def wordMap {X Y : Carrier} (f : X ⟶ Y) : words X ⟶ words Y :=
  arrow (wordRaw f) (wordRaw_partrec f)
    (fun n m h => (mem_words X n).mpr
      (PartialLists.forall₂_source f ((wordRaw_graph f n m).mp h)))
    (fun n m h => (mem_words Y m).mpr
      (PartialLists.forall₂_target f ((wordRaw_graph f n m).mp h)))

theorem mem_wordMap {X Y : Carrier} (f : X ⟶ Y) (n m : ℕ) :
    m ∈ val (wordMap f) n ↔ List.Forall₂ (fun x y => y ∈ val f x)
      (WordCoding.decode n) (WordCoding.decode m) := wordRaw_graph f n m

theorem wordMap_total {X Y : Carrier} (f : X ⟶ Y) (hf : isTotal f) :
    isTotal (wordMap f) := by
  apply (total_iff _).mpr
  intro n hn
  obtain ⟨ys,hys⟩ := Part.dom_iff_mem.mp (PartialLists.traverse_total (WordCoding.decode n)
    (fun x hx => (total_iff f).mp hf x ((mem_words X n).mp hn x hx)))
  exact Part.dom_iff_mem.mpr ⟨WordCoding.encode ys,(Part.mem_map_iff _).mpr ⟨ys,hys,rfl⟩⟩

theorem wordMap_id (X : Carrier) : wordMap (𝟙 X)=𝟙 (words X) := by
  apply val_injective
  apply PFun.ext
  intro n m
  simp only [mem_wordMap,PartialLists.identity_graph]
  change _ ↔ m ∈ val (⊤ : Idem (words X)).hom n
  rw [mem_val_idem,support_top,mem_words]
  have he : WordCoding.decode m=WordCoding.decode n ↔ m=n := by
    constructor
    · intro h
      simpa only [WordCoding.encode_decode] using congrArg WordCoding.encode h
    · intro h; rw [h]
  rw [he,and_comm]

theorem wordMap_comp {X Y Z : Carrier} (f : X ⟶ Y) (g : Y ⟶ Z) :
    wordMap (f ≫ g)=wordMap f ≫ wordMap g := by
  apply val_injective
  apply PFun.ext
  intro n m
  rw [mem_wordMap,PartialLists.composition_graph,mem_val_comp]
  constructor
  · rintro ⟨ys,hy,hy'⟩
    have hn : ys≠[] := by
      intro he
      have hl := hy.length_eq
      rw [he,List.length_nil] at hl
      exact WordCoding.decode_ne_nil n (List.length_eq_zero_iff.mp hl)
    refine ⟨WordCoding.encode ys,(mem_wordMap _ _ _).mpr ?_,(mem_wordMap _ _ _).mpr ?_⟩
    · rwa [WordCoding.decode_encode ys hn]
    · rwa [WordCoding.decode_encode ys hn]
  · rintro ⟨k,hk,hk'⟩
    exact ⟨WordCoding.decode k,(mem_wordMap _ _ _).mp hk,(mem_wordMap _ _ _).mp hk'⟩

def wordIso {X Y : Carrier} (i : X ≅ Y) : words X ≅ words Y where
  hom := wordMap i.hom
  inv := wordMap i.inv
  hom_inv_id := by rw [← wordMap_comp,i.hom_inv_id,wordMap_id]
  inv_hom_id := by rw [← wordMap_comp,i.inv_hom_id,wordMap_id]

end EnumerableCarriers
end CategoricalEssentialIncompleteness.LocalConnectedness
