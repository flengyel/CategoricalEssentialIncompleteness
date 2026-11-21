/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EnumerableWords
public import CategoricalEssentialIncompleteness.PartialListFold
public import CategoricalEssentialIncompleteness.EnumerablePCategory
public import CategoricalEssentialIncompleteness.EnumerableAssociativePrograms

/-! # Singleton insertion, concatenation and finite evaluation -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

def singletonCode (n : ℕ) : ℕ := WordCoding.encode [n]
def concatCode (n : ℕ) : ℕ := WordCoding.encode
  (WordCoding.decode (Nat.unpair n).1 ++ WordCoding.decode (Nat.unpair n).2)

theorem singletonCode_computable : Computable singletonCode :=
  WordCoding.encode_computable.comp
    (Primrec.list_cons.to_comp.comp Computable.id (Computable.const []))

theorem concatCode_computable : Computable concatCode :=
  WordCoding.encode_computable.comp (Primrec.list_append.to_comp.comp
    (WordCoding.decode_computable.comp (Computable.fst.comp Computable.unpair))
    (WordCoding.decode_computable.comp (Computable.snd.comp Computable.unpair)))

theorem decode_singletonCode (n : ℕ) : WordCoding.decode (singletonCode n)=[n] :=
  WordCoding.decode_encode [n] (by simp)

theorem decode_concatCode (n : ℕ) : WordCoding.decode (concatCode n)=
    WordCoding.decode (Nat.unpair n).1 ++ WordCoding.decode (Nat.unpair n).2 :=
  WordCoding.decode_encode _ (by
    intro h
    exact WordCoding.decode_ne_nil _ (List.append_eq_nil_iff.mp h).1)

theorem concatCode_assoc (a b c : ℕ) :
    concatCode (Nat.pair (concatCode (Nat.pair a b)) c)=
      concatCode (Nat.pair a (concatCode (Nat.pair b c))) := by
  conv_lhs => rw [concatCode,Nat.unpair_pair]
  conv_rhs => rw [concatCode,Nat.unpair_pair]
  rw [decode_concatCode,decode_concatCode,Nat.unpair_pair,Nat.unpair_pair,List.append_assoc]

def singleton (X : Carrier) : X ⟶ words X := totalFromFunction singletonCode
  singletonCode_computable (fun n hn => by
    rw [mem_words,decode_singletonCode]
    simpa using hn)

def concatenate (X : Carrier) : product (words X) (words X) ⟶ words X :=
  totalFromFunction concatCode concatCode_computable (fun n hn => by
    rw [mem_words,decode_concatCode]
    exact List.forall_mem_append.mpr ⟨(mem_words X _).mp hn.1,(mem_words X _).mp hn.2⟩)

theorem singleton_total (X : Carrier) : isTotal (singleton X) := totalFromFunction_total _ _ _
theorem concatenate_total (X : Carrier) : isTotal (concatenate X) := totalFromFunction_total _ _ _

theorem mem_concatenate (X : Carrier) (n m : ℕ) :
    m ∈ val (concatenate X) n ↔
      n ∈ (product (words X) (words X)).support ∧ m=concatCode n :=
  mem_totalFromFunction _ _ _ n m

attribute [local irreducible] concatenate

theorem concatenate_associative (X : Carrier) :
    partialProdMap (concatenate X) (𝟙 (words X)) ≫ concatenate X=
      PCategoryStruct.assoc (words X) (words X) (words X) ≫
        partialProdMap (𝟙 (words X)) (concatenate X) ≫ concatenate X := by
  apply associative_of_values (concatenate X) (fun a b => concatCode (Nat.pair a b))
  · intro a ha b hb
    apply Part.eq_some_iff.mpr
    exact (mem_concatenate X _ _).mpr
      ⟨(by simpa only [product,Set.mem_setOf_eq,Nat.unpair_pair] using And.intro ha hb),rfl⟩
  · intro a ha b hb c hc
    exact concatCode_assoc a b c

theorem foldl_target {M : Carrier} (mu : product M M ⟶ M)
    (a : ℕ) (ha : a ∈ M.support) (xs : List ℕ)
    (hxs : ∀ x ∈ xs,x ∈ M.support) {y : ℕ}
    (hy : y ∈ PartialLists.foldl (fun p => val mu (Nat.pair p.1 p.2)) a xs) :
    y ∈ M.support := by
  induction xs generalizing a with
  | nil => exact (Part.mem_some_iff.mp hy) ▸ ha
  | cons x xs ih =>
    obtain ⟨b,hb,hy⟩ := Part.mem_bind_iff.mp hy
    exact ih b (val_target mu _ _ hb) (fun z hz => hxs z (List.mem_cons_of_mem x hz)) hy

theorem foldl_dom {M : Carrier} (mu : product M M ⟶ M) (ht : isTotal mu)
    (a : ℕ) (ha : a ∈ M.support) (xs : List ℕ)
    (hxs : ∀ x ∈ xs,x ∈ M.support) :
    (PartialLists.foldl (fun p => val mu (Nat.pair p.1 p.2)) a xs).Dom := by
  induction xs generalizing a with
  | nil => trivial
  | cons x xs ih =>
    have hp : Nat.pair a x ∈ (product M M).support := by
      simpa only [product,Nat.unpair_pair,Set.mem_setOf_eq] using
        And.intro ha (hxs x List.mem_cons_self)
    obtain ⟨b,hb⟩ := Part.dom_iff_mem.mp ((total_iff mu).mp ht _ hp)
    obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp (ih b (val_target mu _ _ hb)
      (fun z hz => hxs z (List.mem_cons_of_mem x hz)))
    exact Part.dom_iff_mem.mpr ⟨y,Part.mem_bind_iff.mpr ⟨b,hb,hy⟩⟩

def evaluateRaw {Y M : Carrier} (mu : product M M ⟶ M) (f : Y ⟶ M) (n : ℕ) : Part ℕ :=
  (PartialLists.traverse (val f) (WordCoding.decode n)).bind fun ys =>
    PartialLists.foldl (fun p => val mu (Nat.pair p.1 p.2)) (ys.getD 0 0) ys.tail

theorem evaluateRaw_partrec {Y M : Carrier} (mu : product M M ⟶ M) (f : Y ⟶ M) :
    Partrec (evaluateRaw mu f) := by
  have hm : Partrec (fun p : ℕ × ℕ => val mu (Nat.pair p.1 p.2)) :=
    (val_partrec mu).comp Primrec₂.natPair.to_comp
  have hd : Computable (fun xs : List ℕ => (xs.getD 0 0,xs.tail)) :=
    Computable.pair ((Primrec.list_getD 0).to_comp.comp Computable.id (Computable.const 0))
      Primrec.list_tail.to_comp
  exact (((PartialLists.traverse_partrec (val_partrec f)).comp
    WordCoding.decode_computable).bind
      (((PartialLists.foldl_partrec hm).comp hd).comp Computable.snd).to₂)

def evaluate {Y M : Carrier} (mu : product M M ⟶ M) (f : Y ⟶ M) : words Y ⟶ M :=
  arrow (evaluateRaw mu f) (evaluateRaw_partrec mu f)
    (by
      intro n y hy
      obtain ⟨ys,hys,_⟩ := Part.mem_bind_iff.mp hy
      exact (mem_words Y n).mpr
        (PartialLists.forall₂_source f ((PartialLists.mem_traverse _ _ _).mp hys)))
    (by
      intro n y hy
      obtain ⟨ys,hys,hy⟩ := Part.mem_bind_iff.mp hy
      have hs := PartialLists.forall₂_target f ((PartialLists.mem_traverse _ _ _).mp hys)
      have hne : ys≠[] := by
        intro he
        have hl := ((PartialLists.mem_traverse _ _ _).mp hys).length_eq
        rw [he,List.length_nil] at hl
        exact WordCoding.decode_ne_nil n (List.length_eq_zero_iff.mp hl)
      cases ys with
      | nil => exact (hne rfl).elim
      | cons a xs =>
        exact foldl_target mu a (hs a List.mem_cons_self) xs
          (fun z hz => hs z (List.mem_cons_of_mem a hz)) hy)

theorem evaluate_total {Y M : Carrier} (mu : product M M ⟶ M) (ht : isTotal mu)
    (f : Y ⟶ M) (hf : isTotal f) : isTotal (evaluate mu f) := by
  apply (total_iff _).mpr
  intro n hn
  obtain ⟨ys,hys⟩ := Part.dom_iff_mem.mp (PartialLists.traverse_total (WordCoding.decode n)
    (fun x hx => (total_iff f).mp hf x ((mem_words Y n).mp hn x hx)))
  have hs := PartialLists.forall₂_target f ((PartialLists.mem_traverse _ _ _).mp hys)
  have hne : ys≠[] := by
    intro he
    have hl := ((PartialLists.mem_traverse _ _ _).mp hys).length_eq
    rw [he,List.length_nil] at hl
    exact WordCoding.decode_ne_nil n (List.length_eq_zero_iff.mp hl)
  cases ys with
  | nil => exact (hne rfl).elim
  | cons a xs =>
    obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp (foldl_dom mu ht a (hs a List.mem_cons_self) xs
      (fun z hz => hs z (List.mem_cons_of_mem a hz)))
    exact Part.dom_iff_mem.mpr ⟨y,Part.mem_bind_iff.mpr ⟨a::xs,hys,hy⟩⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers
