/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EffectiveForkFunctions

/-! # The explicit product frame on the universal fork -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val)

private theorem comp_pair {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) : Computable (fun x => Nat.pair (f x) (g x)) :=
  Primrec₂.natPair.to_comp.comp hf hg

def splitEndpoint (x : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair (Nat.unpair (Nat.unpair x).1).1 (Nat.unpair (Nat.unpair x).2).1)
    (Nat.pair (Nat.unpair (Nat.unpair x).1).2 (Nat.unpair (Nat.unpair x).2).2)

def mergeEndpoint (x : ℕ) : ℕ := splitEndpoint x

def splitCenter (x : ℕ) : ℕ :=
  let q := quadCode.symm x
  Nat.pair
    (quadCode ((Nat.unpair q.1).1,(Nat.unpair q.2.1).1,
      (Nat.unpair q.2.2.1).1,(Nat.unpair q.2.2.2).1))
    (quadCode ((Nat.unpair q.1).2,(Nat.unpair q.2.1).2,
      (Nat.unpair q.2.2.1).2,(Nat.unpair q.2.2.2).2))

def mergeCenter (x : ℕ) : ℕ :=
  let a := quadCode.symm (Nat.unpair x).1
  let b := quadCode.symm (Nat.unpair x).2
  quadCode (Nat.pair a.1 b.1,Nat.pair a.2.1 b.2.1,
    Nat.pair a.2.2.1 b.2.2.1,Nat.pair a.2.2.2 b.2.2.2)

theorem splitEndpoint_computable : Computable splitEndpoint := by
  have k := Computable.unpair.comp (Computable.fst.comp Computable.unpair)
  have a := Computable.unpair.comp (Computable.snd.comp Computable.unpair)
  exact comp_pair (comp_pair (Computable.fst.comp k) (Computable.fst.comp a))
    (comp_pair (Computable.snd.comp k) (Computable.snd.comp a))

theorem splitCenter_computable : Computable splitCenter := by
  have k := Computable.unpair.comp (Computable.fst.comp quadDecode_computable)
  have z := Computable.unpair.comp (Computable.fst.comp (Computable.snd.comp quadDecode_computable))
  have a := Computable.unpair.comp (Computable.fst.comp
    (Computable.snd.comp (Computable.snd.comp quadDecode_computable)))
  have b := Computable.unpair.comp (Computable.snd.comp
    (Computable.snd.comp (Computable.snd.comp quadDecode_computable)))
  exact comp_pair
    (quadCode_computable.comp (.pair (Computable.fst.comp k)
      (.pair (Computable.fst.comp z) (.pair (Computable.fst.comp a) (Computable.fst.comp b)))))
    (quadCode_computable.comp (.pair (Computable.snd.comp k)
      (.pair (Computable.snd.comp z) (.pair (Computable.snd.comp a) (Computable.snd.comp b)))))

theorem mergeCenter_computable : Computable mergeCenter := by
  have a := quadDecode_computable.comp (Computable.fst.comp Computable.unpair)
  have b := quadDecode_computable.comp (Computable.snd.comp Computable.unpair)
  exact quadCode_computable.comp (.pair (comp_pair (Computable.fst.comp a) (Computable.fst.comp b))
    (.pair (comp_pair (Computable.fst.comp (Computable.snd.comp a)) (Computable.fst.comp (Computable.snd.comp b)))
      (.pair (comp_pair (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp a)))
        (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp b))))
        (comp_pair (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp a)))
          (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp b)))))))

@[simp] theorem merge_split_endpoint (x : ℕ) : mergeEndpoint (splitEndpoint x)=x := by
  simp [mergeEndpoint,splitEndpoint,Nat.pair_unpair]

@[simp] theorem split_merge_endpoint (x : ℕ) : splitEndpoint (mergeEndpoint x)=x :=
  merge_split_endpoint x

@[simp] theorem merge_split_center (x : ℕ) : mergeCenter (splitCenter x)=x := by
  simp [mergeCenter,splitCenter,quadCode,Nat.pair_unpair]

@[simp] theorem split_merge_center (x : ℕ) : splitCenter (mergeCenter x)=x := by
  simp [mergeCenter,splitCenter,quadCode,Nat.pair_unpair]

private theorem prod_support (x : ℕ) :
    x ∈ (EnumerableCarriers.product natCarrier natCarrier).support := ⟨Set.mem_univ _,Set.mem_univ _⟩

theorem split_left (x : ℕ) :
    splitEndpoint (leftCoordinate x)=Nat.pair
      (leftCoordinate (Nat.unpair (splitCenter x)).1)
      (leftCoordinate (Nat.unpair (splitCenter x)).2) := by
  simp [splitEndpoint,leftCoordinate,splitCenter,quadCode]

theorem split_right (x : ℕ) :
    splitEndpoint (rightCoordinate x)=Nat.pair
      (rightCoordinate (Nat.unpair (splitCenter x)).1)
      (rightCoordinate (Nat.unpair (splitCenter x)).2) := by
  simp [splitEndpoint,rightCoordinate,splitCenter,quadCode]

theorem merge_left (x : ℕ) :
    leftCoordinate (mergeCenter x)=mergeEndpoint (Nat.pair
      (leftCoordinate (Nat.unpair x).1) (leftCoordinate (Nat.unpair x).2)) := by
  simp [mergeEndpoint,splitEndpoint,leftCoordinate,mergeCenter,quadCode]

theorem merge_right (x : ℕ) :
    rightCoordinate (mergeCenter x)=mergeEndpoint (Nat.pair
      (rightCoordinate (Nat.unpair x).1) (rightCoordinate (Nat.unpair x).2)) := by
  simp [mergeEndpoint,splitEndpoint,rightCoordinate,mergeCenter,quadCode]

def productFrameForward : V ⟶ product V V :=
  computedMap splitCenter splitEndpoint splitEndpoint splitCenter_computable
    splitEndpoint_computable splitEndpoint_computable
    (fun x _ => prod_support _) (fun x _ => prod_support _) (fun x _ => prod_support _)
    (by
      intro x u hu
      have he := (mem_V_left x u).mp hu
      rw [he,split_left]
      apply (EnumerableCarriers.mem_partialProdMap_iff _ _ _ _).mpr
      simp only [Nat.unpair_pair]
      exact ⟨(mem_V_left _ _).mpr rfl,(mem_V_left _ _).mpr rfl⟩)
    (by
      intro x u hu
      have he := (mem_V_right x u).mp hu
      rw [he,split_right]
      apply (EnumerableCarriers.mem_partialProdMap_iff _ _ _ _).mpr
      simp only [Nat.unpair_pair]
      exact ⟨(mem_V_right _ _).mpr rfl,(mem_V_right _ _).mpr rfl⟩)

def productFrameBackward : product V V ⟶ V :=
  computedMap mergeCenter mergeEndpoint mergeEndpoint mergeCenter_computable
    splitEndpoint_computable splitEndpoint_computable
    (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)
    (by
      intro x u hu
      obtain ⟨h0,h1⟩ := (EnumerableCarriers.mem_partialProdMap_iff _ _ x u).mp hu
      have he : u=Nat.pair (leftCoordinate (Nat.unpair x).1)
          (leftCoordinate (Nat.unpair x).2) := by
        rw [← (mem_V_left _ _).mp h0,← (mem_V_left _ _).mp h1,Nat.pair_unpair]
      exact (mem_V_left _ _).mpr (by rw [he,merge_left]))
    (by
      intro x u hu
      obtain ⟨h0,h1⟩ := (EnumerableCarriers.mem_partialProdMap_iff _ _ x u).mp hu
      have he : u=Nat.pair (rightCoordinate (Nat.unpair x).1)
          (rightCoordinate (Nat.unpair x).2) := by
        rw [← (mem_V_right _ _).mp h0,← (mem_V_right _ _).mp h1,Nat.pair_unpair]
      exact (mem_V_right _ _).mpr (by rw [he,merge_right]))

def productFrame : V ≅ product V V where
  hom := productFrameForward
  inv := productFrameBackward
  hom_inv_id := Hom.ext
    (EnumerableCarriers.totalFromFunction_inverse splitCenter mergeCenter
      splitCenter_computable mergeCenter_computable (fun _ _ => prod_support _)
      (fun _ _ => Set.mem_univ _) (fun x _ => merge_split_center x))
    (EnumerableCarriers.totalFromFunction_inverse splitEndpoint mergeEndpoint
      splitEndpoint_computable splitEndpoint_computable (fun _ _ => prod_support _)
      (fun _ _ => Set.mem_univ _) (fun x _ => merge_split_endpoint x))
    (EnumerableCarriers.totalFromFunction_inverse splitEndpoint mergeEndpoint
      splitEndpoint_computable splitEndpoint_computable (fun _ _ => prod_support _)
      (fun _ _ => Set.mem_univ _) (fun x _ => merge_split_endpoint x))
  inv_hom_id := Hom.ext
    (EnumerableCarriers.totalFromFunction_inverse mergeCenter splitCenter
      mergeCenter_computable splitCenter_computable (fun _ _ => Set.mem_univ _)
      (fun _ _ => prod_support _) (fun x _ => split_merge_center x))
    (EnumerableCarriers.totalFromFunction_inverse mergeEndpoint splitEndpoint
      splitEndpoint_computable splitEndpoint_computable (fun _ _ => Set.mem_univ _)
      (fun _ _ => prod_support _) (fun x _ => split_merge_endpoint x))
    (EnumerableCarriers.totalFromFunction_inverse mergeEndpoint splitEndpoint
      splitEndpoint_computable splitEndpoint_computable (fun _ _ => Set.mem_univ _)
      (fun _ _ => prod_support _) (fun x _ => split_merge_endpoint x))

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
