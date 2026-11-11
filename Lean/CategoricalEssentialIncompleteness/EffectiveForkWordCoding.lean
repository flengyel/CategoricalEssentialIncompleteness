/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.WordTuples
public import CategoricalEssentialIncompleteness.EffectiveForkWords

/-! # The explicit length-preserving word frame functions -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open WordCoding (zipPair zipQuad unpack pack)

def endpointWord (x : ℕ) : List ℕ :=
  zipPair (WordCoding.decode (Nat.unpair x).1)
    (unpack (Nat.unpair (Nat.unpair x).1).1 (Nat.unpair x).2)

def centerWordTuple (q : ℕ × ℕ × ℕ × ℕ) : List ℕ :=
  zipQuad (WordCoding.decode q.1) (unpack (Nat.unpair q.1).1 q.2.1)
    (unpack (Nat.unpair q.1).1 q.2.2.1) (unpack (Nat.unpair q.1).1 q.2.2.2)

def centerWord (x : ℕ) : List ℕ := centerWordTuple (quadCode.symm x)

theorem endpointWord_ne_nil (x : ℕ) : endpointWord x≠[] := by
  intro h
  have hl := congrArg List.length h
  simp only [endpointWord,WordCoding.zipPair_length,List.length_nil] at hl
  exact WordCoding.decode_ne_nil _ (List.length_eq_zero_iff.mp hl)

theorem centerWord_ne_nil (x : ℕ) : centerWord x≠[] := by
  intro h
  have hl := congrArg List.length h
  simp only [centerWord,centerWordTuple,WordCoding.zipQuad,WordCoding.zipPair_length,List.length_nil] at hl
  exact WordCoding.decode_ne_nil _ (List.length_eq_zero_iff.mp hl)

def wordEndpointForward (x : ℕ) : ℕ := WordCoding.encode (endpointWord x)
def wordCenterForward (x : ℕ) : ℕ := WordCoding.encode (centerWord x)

def wordEndpointBackward (x : ℕ) : ℕ :=
  Nat.pair (WordCoding.encode ((WordCoding.decode x).map (fun n => (Nat.unpair n).1)))
    (pack ((WordCoding.decode x).map (fun n => (Nat.unpair n).2)))

def wordCenterBackward (x : ℕ) : ℕ :=
  let xs := WordCoding.decode x
  quadCode (WordCoding.encode (xs.map (fun n => (quadCode.symm n).1)),
    pack (xs.map (fun n => (quadCode.symm n).2.1)),
    pack (xs.map (fun n => (quadCode.symm n).2.2.1)),
    pack (xs.map (fun n => (quadCode.symm n).2.2.2)))

theorem wordEndpointBackward_forward (x : ℕ) :
    wordEndpointBackward (wordEndpointForward x)=x := by
  have hl : (WordCoding.decode (Nat.unpair x).1).length=
      (unpack (Nat.unpair (Nat.unpair x).1).1 (Nat.unpair x).2).length := by
    simp [WordCoding.decode]
  unfold wordEndpointBackward wordEndpointForward
  rw [WordCoding.decode_encode _ (endpointWord_ne_nil x)]
  unfold endpointWord
  rw [WordCoding.zipPair_fst _ _ hl,WordCoding.zipPair_snd _ _ hl,
    WordCoding.encode_decode,WordCoding.pack_unpack,Nat.pair_unpair]

theorem wordCenterBackward_forward (x : ℕ) :
    wordCenterBackward (wordCenterForward x)=x := by
  have hl (a : ℕ) : (WordCoding.decode (quadCode.symm x).1).length=
      (unpack (Nat.unpair (quadCode.symm x).1).1 a).length := by simp [WordCoding.decode]
  obtain ⟨p0,p1,p2,p3⟩ := WordCoding.zipQuad_projections
    (WordCoding.decode (quadCode.symm x).1)
    (unpack (Nat.unpair (quadCode.symm x).1).1 (quadCode.symm x).2.1)
    (unpack (Nat.unpair (quadCode.symm x).1).1 (quadCode.symm x).2.2.1)
    (unpack (Nat.unpair (quadCode.symm x).1).1 (quadCode.symm x).2.2.2)
    (hl _) (hl _) (hl _)
  unfold wordCenterBackward wordCenterForward
  rw [WordCoding.decode_encode _ (centerWord_ne_nil x)]
  dsimp only [centerWord,centerWordTuple]
  rw [p0,p1,p2,p3,WordCoding.encode_decode,WordCoding.pack_unpack,
    WordCoding.pack_unpack,WordCoding.pack_unpack]
  exact quadCode.apply_symm_apply x

theorem wordEndpointForward_backward (x : ℕ) :
    wordEndpointForward (wordEndpointBackward x)=x := by
  have hne : (WordCoding.decode x).map (fun n => (Nat.unpair n).1)≠[] := by
    simpa using WordCoding.decode_ne_nil x
  have hne' : (WordCoding.decode x).map (fun n => (Nat.unpair n).2)≠[] := by
    simpa using WordCoding.decode_ne_nil x
  unfold wordEndpointForward endpointWord wordEndpointBackward
  simp only [Nat.unpair_pair]
  rw [WordCoding.decode_encode _ hne]
  have ht : (Nat.unpair (WordCoding.encode ((WordCoding.decode x).map
      (fun n => (Nat.unpair n).1)))).1=(WordCoding.decode x).length-1 := by
    simp only [WordCoding.encode,Nat.unpair_pair,List.length_map]
  rw [ht]
  have hu : unpack ((WordCoding.decode x).length-1)
      (pack ((WordCoding.decode x).map (fun n => (Nat.unpair n).2)))=
      (WordCoding.decode x).map (fun n => (Nat.unpair n).2) := by
    simpa only [List.length_map] using WordCoding.unpack_pack _ hne'
  rw [hu,WordCoding.zipPair_recover,WordCoding.encode_decode]

theorem wordCenterForward_backward (x : ℕ) :
    wordCenterForward (wordCenterBackward x)=x := by
  have hne (f : ℕ → ℕ) : (WordCoding.decode x).map f≠[] := by
    simpa using WordCoding.decode_ne_nil x
  unfold wordCenterForward centerWord centerWordTuple wordCenterBackward
  simp only [Equiv.symm_apply_apply]
  rw [WordCoding.decode_encode _ (hne _)]
  have ht : (Nat.unpair (WordCoding.encode ((WordCoding.decode x).map
      (fun n => (quadCode.symm n).1)))).1=(WordCoding.decode x).length-1 := by
    simp only [WordCoding.encode,Nat.unpair_pair,List.length_map]
  rw [ht]
  have hu (f : ℕ → ℕ) : unpack ((WordCoding.decode x).length-1)
      (pack ((WordCoding.decode x).map f))=(WordCoding.decode x).map f := by
    simpa only [List.length_map] using WordCoding.unpack_pack _ (hne f)
  rw [hu,hu,hu,WordCoding.zipQuad_recover,WordCoding.encode_decode]

theorem centerWord_left (x : ℕ) :
    (centerWord x).map leftCoordinate=endpointWord (leftCoordinate x) := by
  have hl (a : ℕ) : (WordCoding.decode (quadCode.symm x).1).length=
      (unpack (Nat.unpair (quadCode.symm x).1).1 a).length := by simp [WordCoding.decode]
  have hk : (Nat.unpair (leftCoordinate x)).1=(quadCode.symm x).1 := by
    simp [leftCoordinate,quadCode]
  have hv : (Nat.unpair (leftCoordinate x)).2=(quadCode.symm x).2.2.1 := by
    simp [leftCoordinate,quadCode]
  unfold centerWord centerWordTuple endpointWord
  rw [hk,hv]
  exact WordCoding.zipQuad_left _ _ _ _ (hl _) (hl _) (hl _)

theorem centerWord_right (x : ℕ) :
    (centerWord x).map rightCoordinate=endpointWord (rightCoordinate x) := by
  have hl (a : ℕ) : (WordCoding.decode (quadCode.symm x).1).length=
      (unpack (Nat.unpair (quadCode.symm x).1).1 a).length := by simp [WordCoding.decode]
  have hk : (Nat.unpair (rightCoordinate x)).1=(quadCode.symm x).1 := by
    simp [rightCoordinate,quadCode]
  have hv : (Nat.unpair (rightCoordinate x)).2=(quadCode.symm x).2.2.2 := by
    simp [rightCoordinate,quadCode]
  unfold centerWord centerWordTuple endpointWord
  rw [hk,hv]
  exact WordCoding.zipQuad_right _ _ _ _ (hl _) (hl _) (hl _)

theorem endpointWord_computable : Computable endpointWord :=
  WordCoding.zipPair_computable.comp
    (WordCoding.decode_computable.comp (Computable.fst.comp Computable.unpair))
    (WordCoding.unpack_computable.comp
      (Computable.fst.comp (Computable.unpair.comp (Computable.fst.comp Computable.unpair)))
      (Computable.snd.comp Computable.unpair))

theorem centerWordTuple_computable : Computable centerWordTuple := by
  have hn : Computable (fun q : ℕ × ℕ × ℕ × ℕ => (Nat.unpair q.1).1) :=
    Computable.fst.comp (Computable.unpair.comp Computable.fst)
  have h0 : Computable (fun q : ℕ × ℕ × ℕ × ℕ => WordCoding.decode q.1) :=
    WordCoding.decode_computable.comp Computable.fst
  have h1 : Computable (fun q : ℕ × ℕ × ℕ × ℕ => unpack (Nat.unpair q.1).1 q.2.1) :=
    WordCoding.unpack_computable.comp hn (Computable.fst.comp Computable.snd)
  have h2 : Computable (fun q : ℕ × ℕ × ℕ × ℕ => unpack (Nat.unpair q.1).1 q.2.2.1) :=
    WordCoding.unpack_computable.comp hn (Computable.fst.comp (Computable.snd.comp Computable.snd))
  have h3 : Computable (fun q : ℕ × ℕ × ℕ × ℕ => unpack (Nat.unpair q.1).1 q.2.2.2) :=
    WordCoding.unpack_computable.comp hn (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hd := Computable.pair h0 (Computable.pair h1 (Computable.pair h2 h3))
  have hc := WordCoding.zipQuad_computable.comp hd
  exact hc.of_eq (fun q => rfl)

theorem centerWord_computable : Computable centerWord :=
  centerWordTuple_computable.comp quadDecode_computable

theorem wordEndpointForward_computable : Computable wordEndpointForward :=
  WordCoding.encode_computable.comp endpointWord_computable
theorem wordCenterForward_computable : Computable wordCenterForward :=
  WordCoding.encode_computable.comp centerWord_computable

theorem wordEndpointBackward_computable : Computable wordEndpointBackward := by
  have hk := (Primrec.list_map Primrec.id
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to₂).to_comp.comp
      WordCoding.decode_computable
  have hx := (Primrec.list_map Primrec.id
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to₂).to_comp.comp
      WordCoding.decode_computable
  exact Primrec₂.natPair.to_comp.comp (WordCoding.encode_computable.comp hk)
    (WordCoding.pack_computable.comp hx)

theorem quadDecode_primrec : Primrec quadCode.symm := by
  have ht : Primrec (fun n : ℕ => (Nat.unpair n).2) := Primrec.snd.comp Primrec.unpair
  have htt : Primrec (fun n : ℕ => (Nat.unpair (Nat.unpair n).2).2) := ht.comp ht
  exact Primrec.pair (Primrec.fst.comp Primrec.unpair)
    (Primrec.pair (Primrec.fst.comp (Primrec.unpair.comp ht))
      (Primrec.pair (Primrec.fst.comp (Primrec.unpair.comp htt)) (ht.comp htt)))

theorem wordCenterBackward_computable : Computable wordCenterBackward := by
  have hq (f : ℕ → ℕ) (hf : Primrec f) :
      Computable (fun n => (WordCoding.decode n).map f) :=
    (Primrec.list_map Primrec.id (hf.comp Primrec.snd).to₂).to_comp.comp
      WordCoding.decode_computable
  exact quadCode_computable.comp (Computable.pair
    (WordCoding.encode_computable.comp (hq _ (Primrec.fst.comp quadDecode_primrec)))
    (Computable.pair
      (WordCoding.pack_computable.comp
        (hq _ (Primrec.fst.comp (Primrec.snd.comp quadDecode_primrec))))
      (Computable.pair
        (WordCoding.pack_computable.comp (hq _
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp quadDecode_primrec)))))
        (WordCoding.pack_computable.comp (hq _
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp quadDecode_primrec))))))))

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
