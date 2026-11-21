/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EnumerableWordOperations
public import Mathlib.Algebra.Free

/-! # Nonempty coded words and the free semigroup universal property -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

abbrev Element (X : Carrier) := {n : ℕ // n ∈ X.support}

def typedMap {X Y : Carrier} (f : X ⟶ Y) (hf : isTotal f) (x : Element X) : Element Y :=
  ⟨(val f x.val).get ((total_iff f).mp hf x.val x.property),val_target f _ _ (Part.get_mem _)⟩

theorem typedMap_mem {X Y : Carrier} (f : X ⟶ Y) (hf : isTotal f) (x : Element X) :
    (typedMap f hf x).val ∈ val f x.val := Part.get_mem _

def wordLetters {X : Carrier} (w : FreeSemigroup (Element X)) : List ℕ :=
  (w.head::w.tail).map Subtype.val
def wordCode {X : Carrier} (w : FreeSemigroup (Element X)) : ℕ := WordCoding.encode (wordLetters w)

theorem wordLetters_ne_nil {X : Carrier} (w : FreeSemigroup (Element X)) : wordLetters w≠[] := by
  simp [wordLetters]

theorem decode_wordCode {X : Carrier} (w : FreeSemigroup (Element X)) :
    WordCoding.decode (wordCode w)=wordLetters w := WordCoding.decode_encode _ (wordLetters_ne_nil w)

theorem wordCode_valid {X : Carrier} (w : FreeSemigroup (Element X)) :
    wordCode w ∈ (words X).support := by
  rw [mem_words,decode_wordCode]
  intro n hn
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hn
  exact a.property

def typedLetters (X : Carrier) (xs : List ℕ) (hx : ∀ x ∈ xs,x ∈ X.support) : List (Element X) :=
  xs.attach.map (fun x => ⟨x.val,hx x.val x.property⟩)

theorem typedLetters_values (X : Carrier) (xs : List ℕ) (hx : ∀ x ∈ xs,x ∈ X.support) :
    (typedLetters X xs hx).map Subtype.val=xs := by
  simp [typedLetters,List.map_map]

theorem exists_wordCode (X : Carrier) (n : ℕ) (hn : n ∈ (words X).support) :
    ∃ w : FreeSemigroup (Element X),wordCode w=n := by
  have hs := (mem_words X n).mp hn
  obtain ⟨a,xs,he⟩ := List.exists_cons_of_ne_nil (WordCoding.decode_ne_nil n)
  rw [he] at hs
  let w : FreeSemigroup (Element X) :=
    ⟨⟨a,hs a List.mem_cons_self⟩,typedLetters X xs (fun x hx => hs x (List.mem_cons_of_mem a hx))⟩
  refine ⟨w,?_⟩
  have hw : wordLetters w=a::xs := by
    simp only [wordLetters,w,List.map_cons,typedLetters_values]
  rw [wordCode,hw,← he,WordCoding.encode_decode]

theorem wordCode_mul {X : Carrier} (w v : FreeSemigroup (Element X)) :
    wordCode (w*v)=concatCode (Nat.pair (wordCode w) (wordCode v)) := by
  rw [concatCode,Nat.unpair_pair,decode_wordCode,decode_wordCode]
  simp only [wordCode,wordLetters,
    FreeSemigroup.head_mul,FreeSemigroup.tail_mul,List.map_cons,List.map_append,List.cons_append]

theorem wordCode_injective {X : Carrier} :
    Function.Injective (wordCode (X := X)) := by
  intro w v h
  have hl := congrArg WordCoding.decode h
  rw [decode_wordCode,decode_wordCode] at hl
  have hs := (List.map_injective_iff.mpr Subtype.val_injective) hl
  exact FreeSemigroup.ext (List.cons.inj hs).1 (List.cons.inj hs).2

theorem wordCode_of {X : Carrier} (x : Element X) :
    wordCode (FreeSemigroup.of x)=singletonCode x.val := rfl

theorem foldl_semigroup {M : Carrier} [Semigroup (Element M)]
    (mu : product M M ⟶ M)
    (hm : ∀ a b : Element M,(a*b).val ∈ val mu (Nat.pair a.val b.val))
    {α : Type} (F : α → Element M) (a : Element M) (xs : List α) :
    (xs.foldl (fun b x => b*F x) a).val ∈
      PartialLists.foldl (fun p => val mu (Nat.pair p.1 p.2)) a.val
        (xs.map (fun x => (F x).val)) := by
  induction xs generalizing a with
  | nil => exact Part.mem_some _
  | cons x xs ih => exact Part.mem_bind_iff.mpr ⟨(a*F x).val,hm a (F x),ih (a*F x)⟩

theorem evaluate_wordCode {Y M : Carrier} [Semigroup (Element M)]
    (mu : product M M ⟶ M)
    (hm : ∀ a b : Element M,(a*b).val ∈ val mu (Nat.pair a.val b.val))
    (f : Y ⟶ M) (hf : isTotal f) (w : FreeSemigroup (Element Y)) :
    (FreeSemigroup.lift (typedMap f hf) w).val ∈ val (evaluate mu f) (wordCode w) := by
  let F := typedMap f hf
  have ht : List.Forall₂ (fun x y => y ∈ val f x)
      (wordLetters w) ((w.head::w.tail).map (fun x => (F x).val)) := by
    exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr (fun x hx => typedMap_mem f hf x)))
  change _ ∈ evaluateRaw mu f (wordCode w)
  rw [evaluateRaw,decode_wordCode]
  apply Part.mem_bind_iff.mpr
  refine ⟨_,(PartialLists.mem_traverse _ _ _).mpr ht,?_⟩
  exact foldl_semigroup mu hm F (F w.head) w.tail

theorem evaluate_singleton {Y M : Carrier} (mu : product M M ⟶ M) (f : Y ⟶ M) :
    singleton Y ≫ evaluate mu f=f := by
  apply val_injective
  apply PFun.ext
  intro n y
  rw [mem_val_comp]
  simp only [singleton,mem_totalFromFunction]
  constructor
  · rintro ⟨k,⟨hn,rfl⟩,hy⟩
    change y ∈ evaluateRaw mu f (singletonCode n) at hy
    simpa [evaluateRaw,decode_singletonCode,PartialLists.traverse,PartialLists.foldl,
      Part.bind_assoc,Part.bind_map,Part.bind_some_right] using hy
  · intro hy
    refine ⟨singletonCode n,⟨val_source f n y hy,rfl⟩,?_⟩
    change y ∈ evaluateRaw mu f (singletonCode n)
    simpa [evaluateRaw,decode_singletonCode,PartialLists.traverse,PartialLists.foldl,
      Part.bind_assoc,Part.bind_map,Part.bind_some_right] using hy


theorem mem_evaluate_wordCode {Y M : Carrier} [Semigroup (Element M)]
    (mu : product M M ⟶ M)
    (hm : ∀ a b : Element M,(a*b).val ∈ val mu (Nat.pair a.val b.val))
    (f : Y ⟶ M) (hf : isTotal f) (w : FreeSemigroup (Element Y)) (y : ℕ) :
    y ∈ val (evaluate mu f) (wordCode w) ↔
      y=(FreeSemigroup.lift (typedMap f hf) w).val := by
  exact ⟨fun hy => Part.mem_unique hy (evaluate_wordCode mu hm f hf w),
    fun he => he.symm ▸ evaluate_wordCode mu hm f hf w⟩

theorem evaluate_concatenate {Y M : Carrier} [Semigroup (Element M)]
    (mu : product M M ⟶ M)
    (hm : ∀ a b : Element M,(a*b).val ∈ val mu (Nat.pair a.val b.val))
    (f : Y ⟶ M) (hf : isTotal f) :
    concatenate Y ≫ evaluate mu f=
      partialProdMap (evaluate mu f) (evaluate mu f) ≫ mu := by
  let F := FreeSemigroup.lift (typedMap f hf)
  apply val_injective
  apply PFun.ext
  intro n y
  rw [mem_val_comp,mem_val_comp]
  constructor
  · rintro ⟨k,hk,hy⟩
    obtain ⟨hn,rfl⟩ := (mem_totalFromFunction _ _ _ n k).mp hk
    obtain ⟨w,hw⟩ := exists_wordCode Y (Nat.unpair n).1 hn.1
    obtain ⟨v,hv⟩ := exists_wordCode Y (Nat.unpair n).2 hn.2
    have hc : concatCode n=wordCode (w*v) := by
      rw [wordCode_mul,hw,hv,Nat.pair_unpair]
    rw [hc,mem_evaluate_wordCode mu hm f hf] at hy
    subst y
    refine ⟨Nat.pair (F w).val (F v).val,?_,?_⟩
    · rw [mem_partialProdMap_iff,Nat.unpair_pair,← hw,← hv]
      exact ⟨evaluate_wordCode mu hm f hf w,evaluate_wordCode mu hm f hf v⟩
    · simpa only [map_mul] using hm (F w) (F v)
  · rintro ⟨k,hk,hy⟩
    obtain ⟨h0,h1⟩ := (mem_partialProdMap_iff _ _ n k).mp hk
    obtain ⟨w,hw⟩ := exists_wordCode Y (Nat.unpair n).1 (val_source _ _ _ h0)
    obtain ⟨v,hv⟩ := exists_wordCode Y (Nat.unpair n).2 (val_source _ _ _ h1)
    rw [← hw,mem_evaluate_wordCode mu hm f hf] at h0
    rw [← hv,mem_evaluate_wordCode mu hm f hf] at h1
    have hk' : k=Nat.pair (F w).val (F v).val := by
      rw [← Nat.pair_unpair k,h0,h1]
    rw [hk'] at hy
    have he : y=(F (w*v)).val := by
      have he := Part.mem_unique hy (hm (F w) (F v))
      simpa only [map_mul] using he
    refine ⟨wordCode (w*v),?_,(mem_evaluate_wordCode mu hm f hf _ _).mpr he⟩
    apply (mem_totalFromFunction _ _ _ n _).mpr
    exact ⟨⟨hw ▸ wordCode_valid w,hv ▸ wordCode_valid v⟩,by
      rw [wordCode_mul,hw,hv,Nat.pair_unpair]⟩

theorem evaluate_unique {Y M : Carrier} [Semigroup (Element M)]
    (mu : product M M ⟶ M)
    (hm : ∀ a b : Element M,(a*b).val ∈ val mu (Nat.pair a.val b.val))
    (f : Y ⟶ M) (hf : isTotal f) (k : words Y ⟶ M)
    (hs : singleton Y ≫ k=f)
    (hc : concatenate Y ≫ k=partialProdMap k k ≫ mu) : k=evaluate mu f := by
  let F := FreeSemigroup.lift (typedMap f hf)
  have hval : ∀ w : FreeSemigroup (Element Y),(F w).val ∈ val k (wordCode w) := by
    intro w
    induction w using FreeSemigroup.recOnMul with
    | ih1 x =>
      have h : (typedMap f hf x).val ∈ val (singleton Y ≫ k) x.val := by
        rw [hs]
        exact typedMap_mem f hf x
      obtain ⟨n,hn,hk⟩ := (mem_val_comp _ _ _ _).mp h
      obtain ⟨_,he⟩ := (mem_totalFromFunction _ _ _ _ _).mp hn
      subst n
      exact hk
    | ih2 x v hx hv =>
      have h : (F (FreeSemigroup.of x*v)).val ∈
          val (partialProdMap k k ≫ mu)
            (Nat.pair (wordCode (FreeSemigroup.of x)) (wordCode v)) := by
        apply (mem_val_comp _ _ _ _).mpr
        refine ⟨Nat.pair (F (FreeSemigroup.of x)).val (F v).val,?_,?_⟩
        · apply (mem_partialProdMap_iff _ _ _ _).mpr
          simpa only [Nat.unpair_pair] using And.intro hx hv
        · simpa only [map_mul] using hm (F (FreeSemigroup.of x)) (F v)
      rw [← hc] at h
      obtain ⟨n,hn,hk⟩ := (mem_val_comp _ _ _ _).mp h
      obtain ⟨_,he⟩ := (mem_totalFromFunction _ _ _ _ _).mp hn
      rw [← wordCode_mul] at he
      exact he ▸ hk
  apply val_injective
  apply PFun.ext
  intro n y
  by_cases hn : n ∈ (words Y).support
  · obtain ⟨w,rfl⟩ := exists_wordCode Y n hn
    rw [mem_evaluate_wordCode mu hm f hf]
    exact ⟨fun h => Part.mem_unique h (hval w),fun h => h.symm ▸ hval w⟩
  · exact ⟨fun h => False.elim (hn (val_source k n y h)),
      fun h => False.elim (hn (val_source (evaluate mu f) n y h))⟩

/-- The universal morphism exists in the computable total category, even when the
multiplication is partial off its c.e. carrier. -/
theorem free_semigroup {Y M : Carrier} [Semigroup (Element M)]
    (mu : product M M ⟶ M) (ht : isTotal mu)
    (hm : ∀ a b : Element M,(a*b).val ∈ val mu (Nat.pair a.val b.val))
    (f : Y ⟶ M) (hf : isTotal f) :
    ∃! k : words Y ⟶ M,isTotal k ∧ singleton Y ≫ k=f ∧
      concatenate Y ≫ k=partialProdMap k k ≫ mu := by
  refine ⟨evaluate mu f,⟨evaluate_total mu ht f hf,evaluate_singleton mu f,
    evaluate_concatenate mu hm f hf⟩,?_⟩
  intro k hk
  exact evaluate_unique mu hm f hf k hk.2.1 hk.2.2

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers
