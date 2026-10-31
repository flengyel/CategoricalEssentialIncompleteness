/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EffectiveForkWordCoding

/-! # The nonempty-word frame on the universal fork -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val)

theorem wordNat_support (n : ℕ) : n ∈ (EnumerableCarriers.words natCarrier).support :=
  (EnumerableCarriers.mem_words natCarrier n).mpr (fun _ _ => Set.mem_univ _)

theorem wordFrame_forward_left (x : ℕ) :
    wordEndpointForward (leftCoordinate x) ∈
      val (EnumerableCarriers.wordMap V.leftMap) (wordCenterForward x) := by
  rw [EnumerableCarriers.mem_wordMap V.leftMap]
  unfold wordCenterForward wordEndpointForward
  rw [WordCoding.decode_encode _ (centerWord_ne_nil x),
    WordCoding.decode_encode _ (endpointWord_ne_nil _),← centerWord_left]
  rw [List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr (fun z _ => (mem_V_left z _).mpr rfl)

theorem wordFrame_forward_right (x : ℕ) :
    wordEndpointForward (rightCoordinate x) ∈
      val (EnumerableCarriers.wordMap V.rightMap) (wordCenterForward x) := by
  rw [EnumerableCarriers.mem_wordMap V.rightMap]
  unfold wordCenterForward wordEndpointForward
  rw [WordCoding.decode_encode _ (centerWord_ne_nil x),
    WordCoding.decode_encode _ (endpointWord_ne_nil _),← centerWord_right]
  rw [List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr (fun z _ => (mem_V_right z _).mpr rfl)

attribute [local irreducible] wordCenterForward wordEndpointForward
  wordCenterBackward wordEndpointBackward

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def wordForwardCenterArrow : natCarrier ⟶ EnumerableCarriers.words natCarrier :=
  EnumerableCarriers.totalFromFunction
    (X := natCarrier) (Y := EnumerableCarriers.words natCarrier) wordCenterForward wordCenterForward_computable
    (fun x _ => wordNat_support (wordCenterForward x))

def wordForwardEndpointArrow : natCarrier ⟶ EnumerableCarriers.words natCarrier :=
  EnumerableCarriers.totalFromFunction
    (X := natCarrier) (Y := EnumerableCarriers.words natCarrier) wordEndpointForward wordEndpointForward_computable
    (fun x _ => wordNat_support (wordEndpointForward x))

def wordBackwardCenterArrow : EnumerableCarriers.words natCarrier ⟶ natCarrier :=
  EnumerableCarriers.totalFromFunction
    (X := EnumerableCarriers.words natCarrier) (Y := natCarrier) wordCenterBackward wordCenterBackward_computable
    (fun x _ => Set.mem_univ (wordCenterBackward x))

def wordBackwardEndpointArrow : EnumerableCarriers.words natCarrier ⟶ natCarrier :=
  EnumerableCarriers.totalFromFunction
    (X := EnumerableCarriers.words natCarrier) (Y := natCarrier) wordEndpointBackward wordEndpointBackward_computable
    (fun x _ => Set.mem_univ (wordEndpointBackward x))

def wordFrameForward : V ⟶ words V where
  center := wordForwardCenterArrow
  left := wordForwardEndpointArrow
  right := wordForwardEndpointArrow
  natural_left := by
    intro x y u v hxy hxu hyv
    obtain ⟨_,he⟩ := (EnumerableCarriers.mem_totalFromFunction
      (X := natCarrier) (Y := EnumerableCarriers.words natCarrier) wordCenterForward
      wordCenterForward_computable (fun x _ => wordNat_support (wordCenterForward x)) x y).mp hxy
    subst y
    have hu := (mem_V_left x u).mp hxu
    subst u
    exact (EnumerableCarriers.mem_totalFromFunction
      (X := natCarrier) (Y := EnumerableCarriers.words natCarrier) wordEndpointForward
      wordEndpointForward_computable (fun x _ => wordNat_support (wordEndpointForward x)) _ v).mpr
      ⟨Set.mem_univ _,Part.mem_unique hyv (wordFrame_forward_left x)⟩
  natural_right := by
    intro x y u v hxy hxu hyv
    obtain ⟨_,he⟩ := (EnumerableCarriers.mem_totalFromFunction
      (X := natCarrier) (Y := EnumerableCarriers.words natCarrier) wordCenterForward
      wordCenterForward_computable (fun x _ => wordNat_support (wordCenterForward x)) x y).mp hxy
    subst y
    have hu := (mem_V_right x u).mp hxu
    subst u
    exact (EnumerableCarriers.mem_totalFromFunction
      (X := natCarrier) (Y := EnumerableCarriers.words natCarrier) wordEndpointForward
      wordEndpointForward_computable (fun x _ => wordNat_support (wordEndpointForward x)) _ v).mpr
      ⟨Set.mem_univ _,Part.mem_unique hyv (wordFrame_forward_right x)⟩

theorem word_center_reverse (y x : ℕ) :
    x ∈ val wordBackwardCenterArrow y ↔ y ∈ val wordForwardCenterArrow x := by
  have hb := EnumerableCarriers.mem_totalFromFunction
    (X := EnumerableCarriers.words natCarrier) (Y := natCarrier) wordCenterBackward
    wordCenterBackward_computable (fun x _ => Set.mem_univ (wordCenterBackward x)) y x
  have hf := EnumerableCarriers.mem_totalFromFunction
    (X := natCarrier) (Y := EnumerableCarriers.words natCarrier) wordCenterForward
    wordCenterForward_computable (fun x _ => wordNat_support (wordCenterForward x)) x y
  constructor
  · intro h
    obtain ⟨_,hx⟩ := hb.mp h
    apply hf.mpr
    exact ⟨Set.mem_univ x,by rw [hx,wordCenterForward_backward]⟩
  · intro h
    obtain ⟨_,hy⟩ := hf.mp h
    apply hb.mpr
    exact ⟨wordNat_support y,by rw [hy,wordCenterBackward_forward]⟩

theorem word_endpoint_reverse (y x : ℕ) :
    x ∈ val wordBackwardEndpointArrow y ↔ y ∈ val wordForwardEndpointArrow x := by
  have hb := EnumerableCarriers.mem_totalFromFunction
    (X := EnumerableCarriers.words natCarrier) (Y := natCarrier) wordEndpointBackward
    wordEndpointBackward_computable (fun x _ => Set.mem_univ (wordEndpointBackward x)) y x
  have hf := EnumerableCarriers.mem_totalFromFunction
    (X := natCarrier) (Y := EnumerableCarriers.words natCarrier) wordEndpointForward
    wordEndpointForward_computable (fun x _ => wordNat_support (wordEndpointForward x)) x y
  constructor
  · intro h
    obtain ⟨_,hx⟩ := hb.mp h
    apply hf.mpr
    exact ⟨Set.mem_univ x,by rw [hx,wordEndpointForward_backward]⟩
  · intro h
    obtain ⟨_,hy⟩ := hf.mp h
    apply hb.mpr
    exact ⟨wordNat_support y,by rw [hy,wordEndpointBackward_forward]⟩


def wordFrameBackward : words V ⟶ V where
  center := wordBackwardCenterArrow
  left := wordBackwardEndpointArrow
  right := wordBackwardEndpointArrow
  natural_left := respects_inverse wordFrameForward.natural_left
    wordBackwardCenterArrow wordBackwardEndpointArrow word_center_reverse word_endpoint_reverse
  natural_right := respects_inverse wordFrameForward.natural_right
    wordBackwardCenterArrow wordBackwardEndpointArrow word_center_reverse word_endpoint_reverse

def wordFrame : V ≅ words V where
  hom := wordFrameForward
  inv := wordFrameBackward
  hom_inv_id := Hom.ext
    (EnumerableCarriers.totalFromFunction_inverse
      (X := natCarrier) (Y := EnumerableCarriers.words natCarrier) wordCenterForward wordCenterBackward
      wordCenterForward_computable wordCenterBackward_computable (fun _ _ => wordNat_support _)
      (fun x _ => Set.mem_univ (wordCenterBackward x)) (fun x _ => wordCenterBackward_forward x))
    (EnumerableCarriers.totalFromFunction_inverse
      (X := natCarrier) (Y := EnumerableCarriers.words natCarrier) wordEndpointForward wordEndpointBackward
      wordEndpointForward_computable wordEndpointBackward_computable (fun _ _ => wordNat_support _)
      (fun x _ => Set.mem_univ (wordEndpointBackward x)) (fun x _ => wordEndpointBackward_forward x))
    (EnumerableCarriers.totalFromFunction_inverse
      (X := natCarrier) (Y := EnumerableCarriers.words natCarrier) wordEndpointForward wordEndpointBackward
      wordEndpointForward_computable wordEndpointBackward_computable (fun _ _ => wordNat_support _)
      (fun x _ => Set.mem_univ (wordEndpointBackward x)) (fun x _ => wordEndpointBackward_forward x))
  inv_hom_id := Hom.ext
    (EnumerableCarriers.totalFromFunction_inverse
      (X := EnumerableCarriers.words natCarrier) (Y := natCarrier) wordCenterBackward wordCenterForward
      wordCenterBackward_computable wordCenterForward_computable (fun _ _ => Set.mem_univ _)
      (fun x _ => wordNat_support (wordCenterForward x)) (fun x _ => wordCenterForward_backward x))
    (EnumerableCarriers.totalFromFunction_inverse
      (X := EnumerableCarriers.words natCarrier) (Y := natCarrier) wordEndpointBackward wordEndpointForward
      wordEndpointBackward_computable wordEndpointForward_computable (fun _ _ => Set.mem_univ _)
      (fun x _ => wordNat_support (wordEndpointForward x)) (fun x _ => wordEndpointForward_backward x))
    (EnumerableCarriers.totalFromFunction_inverse
      (X := EnumerableCarriers.words natCarrier) (Y := natCarrier) wordEndpointBackward wordEndpointForward
      wordEndpointBackward_computable wordEndpointForward_computable (fun _ _ => Set.mem_univ _)
      (fun x _ => wordNat_support (wordEndpointForward x)) (fun x _ => wordEndpointForward_backward x))

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
