/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnumerableFreeSemigroup
import CategoricalEssentialIncompleteness.EnumerableInternalSemigroup
import CategoricalEssentialIncompleteness.EffectiveForkWords
import CategoricalEssentialIncompleteness.EffectiveForkProducts

/-! # Free semigroups in the actual total fork category -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val Element)

theorem respects_singleton {C A : Carrier} (r : C ⟶ A) :
    Respects r (EnumerableCarriers.wordMap r)
      (EnumerableCarriers.singleton C) (EnumerableCarriers.singleton A) := by
  intro x y u v hxy hxu hyv
  obtain ⟨hx,rfl⟩ := (EnumerableCarriers.mem_totalFromFunction _ _ _ _ _).mp hxy
  have hp : EnumerableCarriers.singletonCode u ∈
      val (EnumerableCarriers.wordMap r) (EnumerableCarriers.singletonCode x) := by
    rw [EnumerableCarriers.mem_wordMap,EnumerableCarriers.decode_singletonCode,
      EnumerableCarriers.decode_singletonCode]
    exact List.Forall₂.cons hxu List.Forall₂.nil
  apply (EnumerableCarriers.mem_totalFromFunction _ _ _ _ _).mpr
  exact ⟨EnumerableCarriers.val_target r x u hxu,Part.mem_unique hyv hp⟩

theorem respects_concatenate {C A : Carrier} (r : C ⟶ A) :
    Respects (EnumerableCarriers.partialProdMap (EnumerableCarriers.wordMap r)
      (EnumerableCarriers.wordMap r)) (EnumerableCarriers.wordMap r)
      (EnumerableCarriers.concatenate C) (EnumerableCarriers.concatenate A) := by
  intro x y u v hxy hxu hyv
  obtain ⟨hx,rfl⟩ := (EnumerableCarriers.mem_totalFromFunction _ _ _ _ _).mp hxy
  obtain ⟨h0,h1⟩ := (EnumerableCarriers.mem_partialProdMap_iff _ _ _ _).mp hxu
  have hp : EnumerableCarriers.concatCode u ∈
      val (EnumerableCarriers.wordMap r) (EnumerableCarriers.concatCode x) := by
    rw [EnumerableCarriers.mem_wordMap,EnumerableCarriers.decode_concatCode,
      EnumerableCarriers.decode_concatCode]
    exact List.rel_append ((EnumerableCarriers.mem_wordMap _ _ _).mp h0)
      ((EnumerableCarriers.mem_wordMap _ _ _).mp h1)
  apply (EnumerableCarriers.mem_totalFromFunction _ _ _ _ _).mpr
  exact ⟨EnumerableCarriers.val_target _ _ _ hxu,Part.mem_unique hyv hp⟩

def wordSingleton (Y : Object) : Y ⟶ words Y :=
  ⟨EnumerableCarriers.singleton Y.center,EnumerableCarriers.singleton Y.left,
    EnumerableCarriers.singleton Y.right,respects_singleton Y.leftMap,
    respects_singleton Y.rightMap⟩

def wordConcatenate (Y : Object) : product (words Y) (words Y) ⟶ words Y :=
  ⟨EnumerableCarriers.concatenate Y.center,EnumerableCarriers.concatenate Y.left,
    EnumerableCarriers.concatenate Y.right,respects_concatenate Y.leftMap,
    respects_concatenate Y.rightMap⟩

theorem wordSingleton_total (Y : Object) : isTotal (wordSingleton Y) :=
  (total_iff _).mpr ⟨EnumerableCarriers.singleton_total _,
    EnumerableCarriers.singleton_total _,EnumerableCarriers.singleton_total _⟩

theorem wordConcatenate_total (Y : Object) : isTotal (wordConcatenate Y) :=
  (total_iff _).mpr ⟨EnumerableCarriers.concatenate_total _,
    EnumerableCarriers.concatenate_total _,EnumerableCarriers.concatenate_total _⟩

theorem respects_foldl {C A : Carrier} (r : C ⟶ A) (hr : isTotal r)
    (mu : EnumerableCarriers.product C C ⟶ C)
    (nu : EnumerableCarriers.product A A ⟶ A)
    (hm : Respects (EnumerableCarriers.partialProdMap r r) r mu nu)
    (xs us : List ℕ) (hxu : List.Forall₂ (fun x u => u ∈ val r x) xs us)
    (hs : ∀ x ∈ xs,x ∈ C.support) (a u : ℕ) (ha : a ∈ C.support)
    (hau : u ∈ val r a) (y v : ℕ)
    (hy : y ∈ PartialLists.foldl (fun p => val mu (Nat.pair p.1 p.2)) a xs)
    (hyv : v ∈ val r y) :
    v ∈ PartialLists.foldl (fun p => val nu (Nat.pair p.1 p.2)) u us := by
  induction hxu generalizing a u with
  | nil =>
    have he : y=a := Part.mem_some_iff.mp hy
    subst y
    exact Part.mem_some_iff.mpr (Part.mem_unique hyv hau)
  | @cons x x' xs us hxx' hxu ih =>
    obtain ⟨b,hb,hby⟩ := Part.mem_bind_iff.mp hy
    have hbC := EnumerableCarriers.val_target mu _ _ hb
    obtain ⟨b',hbb'⟩ := Part.dom_iff_mem.mp ((EnumerableCarriers.total_iff r).mp hr b hbC)
    have hnu : b' ∈ val nu (Nat.pair u x') := hm (Nat.pair a x) b (Nat.pair u x') b'
      hb ((EnumerableCarriers.mem_partialProdMap_iff _ _ _ _).mpr
        (by simpa only [Nat.unpair_pair] using And.intro hau hxx')) hbb'
    exact Part.mem_bind_iff.mpr ⟨b',hnu,ih
      (fun z hz => hs z (List.mem_cons_of_mem x hz)) b b' hbC hbb' hby⟩

theorem respects_evaluate {Y Y' M M' : Carrier}
    (r : Y ⟶ Y') (s : M ⟶ M') (hs : isTotal s)
    (mu : EnumerableCarriers.product M M ⟶ M)
    (nu : EnumerableCarriers.product M' M' ⟶ M')
    (hm : Respects (EnumerableCarriers.partialProdMap s s) s mu nu)
    (f : Y ⟶ M) (g : Y' ⟶ M') (hf : Respects r s f g) :
    Respects (EnumerableCarriers.wordMap r) s
      (EnumerableCarriers.evaluate mu f) (EnumerableCarriers.evaluate nu g) := by
  intro x y u v hxy hxu hyv
  change y ∈ EnumerableCarriers.evaluateRaw mu f x at hxy
  obtain ⟨zs,hzs,hzy⟩ := Part.mem_bind_iff.mp hxy
  have hfs := (PartialLists.mem_traverse _ _ _).mp hzs
  have hzM := PartialLists.forall₂_target f hfs
  obtain ⟨vs,hvs⟩ := Part.dom_iff_mem.mp (PartialLists.traverse_total zs
    (fun z hz => (EnumerableCarriers.total_iff s).mp hs z (hzM z hz)))
  have hzs' := (PartialLists.mem_traverse _ _ _).mp hvs
  have hgu := respects_lists hf hfs
    ((EnumerableCarriers.mem_wordMap _ _ _).mp hxu) hzs'
  change v ∈ EnumerableCarriers.evaluateRaw nu g u
  apply Part.mem_bind_iff.mpr
  refine ⟨vs,(PartialLists.mem_traverse _ _ _).mpr hgu,?_⟩
  have hne : zs≠[] := by
    intro he
    have hl := hfs.length_eq
    rw [he,List.length_nil] at hl
    exact WordCoding.decode_ne_nil x (List.length_eq_zero_iff.mp hl)
  cases hzs' with
  | nil => exact (hne rfl).elim
  | @cons a b zs vs hab habs =>
    exact respects_foldl s hs mu nu hm zs vs habs
      (fun z hz => hzM z (List.mem_cons_of_mem a hz)) a b
      (hzM a List.mem_cons_self) hab y v hzy hyv

def evaluate {Y M : Object} (mu : product M M ⟶ M) (f : Y ⟶ M) : words Y ⟶ M :=
  ⟨EnumerableCarriers.evaluate mu.center f.center,
    EnumerableCarriers.evaluate mu.left f.left,
    EnumerableCarriers.evaluate mu.right f.right,
    respects_evaluate Y.leftMap M.leftMap M.left_total mu.center mu.left
      mu.natural_left f.center f.left f.natural_left,
    respects_evaluate Y.rightMap M.rightMap M.right_total mu.center mu.right
      mu.natural_right f.center f.right f.natural_right⟩

theorem evaluate_total {Y M : Object} (mu : product M M ⟶ M) (ht : isTotal mu)
    (f : Y ⟶ M) (hf : isTotal f) : isTotal (evaluate mu f) := by
  obtain ⟨hm0,hm1,hm2⟩ := (total_iff mu).mp ht
  obtain ⟨hf0,hf1,hf2⟩ := (total_iff f).mp hf
  exact (total_iff _).mpr ⟨EnumerableCarriers.evaluate_total _ hm0 _ hf0,
    EnumerableCarriers.evaluate_total _ hm1 _ hf1,EnumerableCarriers.evaluate_total _ hm2 _ hf2⟩

theorem evaluate_singleton {Y M : Object} (mu : product M M ⟶ M) (f : Y ⟶ M) :
    wordSingleton Y ≫ evaluate mu f=f :=
  Hom.ext (EnumerableCarriers.evaluate_singleton _ _) (EnumerableCarriers.evaluate_singleton _ _)
    (EnumerableCarriers.evaluate_singleton _ _)

/-- Component semigroup structures are required to be computed by the actual
internal multiplication arrow. No total extension off the carriers is imposed. -/
theorem free_semigroup {Y M : Object}
    [Semigroup (Element M.center)] [Semigroup (Element M.left)] [Semigroup (Element M.right)]
    (mu : product M M ⟶ M) (ht : isTotal mu)
    (hm0 : ∀ a b : Element M.center,(a*b).val ∈ val mu.center (Nat.pair a.val b.val))
    (hm1 : ∀ a b : Element M.left,(a*b).val ∈ val mu.left (Nat.pair a.val b.val))
    (hm2 : ∀ a b : Element M.right,(a*b).val ∈ val mu.right (Nat.pair a.val b.val))
    (f : Y ⟶ M) (hf : isTotal f) :
    ∃! k : words Y ⟶ M,isTotal k ∧ wordSingleton Y ≫ k=f ∧
      wordConcatenate Y ≫ k=productMap k k ≫ mu := by
  obtain ⟨hf0,hf1,hf2⟩ := (total_iff f).mp hf
  refine ⟨evaluate mu f,⟨evaluate_total mu ht f hf,evaluate_singleton mu f,?_⟩,?_⟩
  · exact Hom.ext (EnumerableCarriers.evaluate_concatenate _ hm0 _ hf0)
      (EnumerableCarriers.evaluate_concatenate _ hm1 _ hf1)
      (EnumerableCarriers.evaluate_concatenate _ hm2 _ hf2)
  · intro k hk
    exact Hom.ext
      (EnumerableCarriers.evaluate_unique _ hm0 _ hf0 k.center
        (congrArg Hom.center hk.2.1) (congrArg Hom.center hk.2.2))
      (EnumerableCarriers.evaluate_unique _ hm1 _ hf1 k.left
        (congrArg Hom.left hk.2.1) (congrArg Hom.left hk.2.2))
      (EnumerableCarriers.evaluate_unique _ hm2 _ hf2 k.right
        (congrArg Hom.right hk.2.1) (congrArg Hom.right hk.2.2))

structure InternalSemigroup where
  carrier : Object
  multiplication : product carrier carrier ⟶ carrier
  total : isTotal multiplication
  associative : productMap multiplication (𝟙 carrier) ≫ multiplication=
    PCategoryStruct.assoc carrier carrier carrier ≫
      productMap (𝟙 carrier) multiplication ≫ multiplication

theorem wordConcatenate_associative (Y : Object) :
    productMap (wordConcatenate Y) (𝟙 (words Y)) ≫ wordConcatenate Y=
      PCategoryStruct.assoc (words Y) (words Y) (words Y) ≫
        productMap (𝟙 (words Y)) (wordConcatenate Y) ≫ wordConcatenate Y :=
  Hom.ext (EnumerableCarriers.concatenate_associative _)
    (EnumerableCarriers.concatenate_associative _) (EnumerableCarriers.concatenate_associative _)

def wordInternalSemigroup (Y : Object) : InternalSemigroup where
  carrier := words Y
  multiplication := wordConcatenate Y
  total := wordConcatenate_total Y
  associative := wordConcatenate_associative Y

/-- The manuscript's free-semigroup property, for every actual internal
semigroup and total arrow. Component algebra structures are derived here. -/
theorem internal_free_semigroup (M : InternalSemigroup) (Y : Object)
    (f : Y ⟶ M.carrier) (hf : isTotal f) :
    ∃! k : words Y ⟶ M.carrier,isTotal k ∧ wordSingleton Y ≫ k=f ∧
      wordConcatenate Y ≫ k=productMap k k ≫ M.multiplication := by
  let mu := M.multiplication
  obtain ⟨ht0,ht1,ht2⟩ := (total_iff mu).mp M.total
  have ha0 : EnumerableCarriers.partialProdMap mu.center (𝟙 M.carrier.center) ≫ mu.center=
      PCategoryStruct.assoc M.carrier.center M.carrier.center M.carrier.center ≫
        EnumerableCarriers.partialProdMap (𝟙 M.carrier.center) mu.center ≫ mu.center :=
    congrArg Hom.center M.associative
  have ha1 : EnumerableCarriers.partialProdMap mu.left (𝟙 M.carrier.left) ≫ mu.left=
      PCategoryStruct.assoc M.carrier.left M.carrier.left M.carrier.left ≫
        EnumerableCarriers.partialProdMap (𝟙 M.carrier.left) mu.left ≫ mu.left :=
    congrArg Hom.left M.associative
  have ha2 : EnumerableCarriers.partialProdMap mu.right (𝟙 M.carrier.right) ≫ mu.right=
      PCategoryStruct.assoc M.carrier.right M.carrier.right M.carrier.right ≫
        EnumerableCarriers.partialProdMap (𝟙 M.carrier.right) mu.right ≫ mu.right :=
    congrArg Hom.right M.associative
  letI := EnumerableCarriers.semigroupOfMultiplication mu.center ht0 ha0
  letI := EnumerableCarriers.semigroupOfMultiplication mu.left ht1 ha1
  letI := EnumerableCarriers.semigroupOfMultiplication mu.right ht2 ha2
  exact free_semigroup mu M.total (EnumerableCarriers.multiplyValue_mem _ ht0)
    (EnumerableCarriers.multiplyValue_mem _ ht1) (EnumerableCarriers.multiplyValue_mem _ ht2) f hf

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
