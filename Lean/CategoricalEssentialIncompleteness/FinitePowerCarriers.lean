/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnumerableCarriers

/-! # Coding c.e. subsets of finite powers and their partial recursive maps -/

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory Encodable

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

variable {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]

def codeSupport (A : Set α) : Set ℕ := {n | ∃ a ∈ A, encode a = n}

theorem codeSupport_re (A : Set α) (hA : REPred (· ∈ A)) : REPred (· ∈ codeSupport A) := by
  exact ((REPred.comp Computable.snd hA).and
    (Primrec.eq.comp (Primrec.encode.comp Primrec.snd) Primrec.fst).computablePred.to_re).projection

def codedCarrier (A : Set α) (hA : REPred (· ∈ A)) : Carrier :=
  ⟨codeSupport A, codeSupport_re A hA⟩

@[simp] theorem encode_mem_codeSupport (A : Set α) (a : α) :
    encode a ∈ codeSupport A ↔ a ∈ A := by
  constructor
  · rintro ⟨b, hb, he⟩
    exact encode_injective he ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- Canonical codes rule out extraneous inputs accepted by an arbitrary decoder. -/
def codedPartial (f : α → Part β) (n : ℕ) : Part ℕ :=
  Part.bind (Part.ofOption (decode₂ α n)) (fun a => (f a).map encode)

theorem codedPartial_partrec {f : α → Part β} (hf : Partrec f) : Partrec (codedPartial f) :=
  Partrec.nat_iff.mpr (Partrec.bind_decode₂_iff.mp hf)

@[simp] theorem codedPartial_encode (f : α → Part β) (a : α) :
    codedPartial f (encode a) = (f a).map encode := by
  simp [codedPartial, decode₂_encode]

theorem mem_codedPartial (f : α → Part β) (n m : ℕ) :
    m ∈ codedPartial f n ↔ ∃ a b, encode a = n ∧ b ∈ f a ∧ encode b = m := by
  simp only [codedPartial, Part.mem_bind_iff, Part.mem_ofOption, mem_decode₂, Part.mem_map_iff]
  aesop

theorem codedPartial_injective : Function.Injective (codedPartial (α := α) (β := β)) := by
  intro f g he
  funext a
  apply Part.ext
  intro b
  have hh : encode b ∈ codedPartial f (encode a) ↔ encode b ∈ codedPartial g (encode a) := by
    rw [he]
  simpa only [codedPartial_encode, Part.mem_map_iff, encode_injective.eq_iff,
    exists_eq_right] using hh

def codedArrow {A : Set α} {B : Set β} (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (f : α → Part β) (hf : Partrec f)
    (hs : ∀ a b, b ∈ f a → a ∈ A) (ht : ∀ a b, b ∈ f a → b ∈ B) :
    codedCarrier A hA ⟶ codedCarrier B hB :=
  arrow (codedPartial f) (codedPartial_partrec hf)
    (by
      intro n m h
      obtain ⟨a, b, rfl, hab, _⟩ := (mem_codedPartial f n m).mp h
      exact (encode_mem_codeSupport A a).mpr (hs a b hab))
    (by
      intro n m h
      obtain ⟨a, b, _, hab, rfl⟩ := (mem_codedPartial f n m).mp h
      exact (encode_mem_codeSupport B b).mpr (ht a b hab))

theorem codedArrow_total {A : Set α} {B : Set β}
    (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (f : α → Part β) (hf : Partrec f)
    (hs : ∀ a b, b ∈ f a → a ∈ A) (ht : ∀ a b, b ∈ f a → b ∈ B) :
    isTotal (codedArrow hA hB f hf hs ht) ↔ ∀ a ∈ A, (f a).Dom := by
  rw [total_iff]
  constructor
  · intro h a ha
    obtain ⟨m, hm⟩ := Part.dom_iff_mem.mp (h (encode a)
      ((encode_mem_codeSupport A a).mpr ha))
    obtain ⟨a', b, he, hab, _⟩ := (mem_codedPartial f (encode a) m).mp hm
    have he' : a' = a := encode_injective he
    exact he' ▸ Part.dom_iff_mem.mpr ⟨b, hab⟩
  · intro h n hn
    obtain ⟨a, ha, rfl⟩ := hn
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp (h a ha)
    exact Part.dom_iff_mem.mpr ⟨encode b,
      (mem_codedPartial f (encode a) (encode b)).mpr ⟨a, b, rfl, hb, rfl⟩⟩

theorem codedPartial_comp (f : α → Part β) (g : β → Part γ) :
    codedPartial (fun a => (f a).bind g) =
      fun n => (codedPartial f n).bind (codedPartial g) := by
  funext n
  apply Part.ext
  intro m
  simp only [mem_codedPartial, Part.mem_bind_iff]
  constructor
  · rintro ⟨a, c, ha, ⟨b, hab, hbc⟩, hc⟩
    exact ⟨encode b, ⟨a, b, ha, hab, rfl⟩, b, c, rfl, hbc, hc⟩
  · rintro ⟨k, ⟨a, b, ha, hab, hb⟩, b', c, hb', hbc, hc⟩
    have he : b' = b := encode_injective (hb'.trans hb.symm)
    subst b'
    exact ⟨a, c, ha, ⟨b, hab, hbc⟩, hc⟩

def decodedPartial (f : ℕ → Part ℕ) (a : α) : Part β :=
  (f (encode a)).bind (fun n => Part.ofOption (decode₂ β n))

theorem decodedPartial_partrec {f : ℕ → Part ℕ} (hf : Partrec f) :
    Partrec (decodedPartial (α := α) (β := β) f) :=
  (hf.comp Computable.encode).bind
    ((Computable.ofOption Primrec.decode₂.to_comp).comp Computable.snd).to₂

theorem mem_decodedPartial (f : ℕ → Part ℕ) (a : α) (b : β) :
    b ∈ decodedPartial f a ↔ encode b ∈ f (encode a) := by
  simp only [decodedPartial, Part.mem_bind_iff, Part.mem_ofOption, mem_decode₂]
  aesop

theorem decoded_coded (f : α → Part β) : decodedPartial (codedPartial f) = f := by
  funext a
  apply Part.ext
  intro b
  simp only [mem_decodedPartial, codedPartial_encode, Part.mem_map_iff,
    encode_injective.eq_iff, exists_eq_right]

/-- Every actual arrow between coded carriers comes from an ambient partial recursive map. -/
theorem coded_decoded {A : Set α} {B : Set β}
    (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (f : codedCarrier A hA ⟶ codedCarrier B hB) :
    codedPartial (decodedPartial (α := α) (β := β) (val f)) = val f := by
  funext n
  apply Part.ext
  intro m
  constructor
  · intro h
    obtain ⟨a, b, he, hab, hb⟩ := (mem_codedPartial _ n m).mp h
    have hh := (mem_decodedPartial (val f) a b).mp hab
    rwa [he, hb] at hh
  · intro hm
    obtain ⟨a, _, ha⟩ := val_source f n m hm
    obtain ⟨b, _, hb⟩ := val_target f n m hm
    exact (mem_codedPartial _ n m).mpr ⟨a, b, ha,
      (mem_decodedPartial (val f) a b).mpr (by rwa [ha, hb]), hb⟩

theorem decoded_source {A : Set α} {B : Set β}
    (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (f : codedCarrier A hA ⟶ codedCarrier B hB) (a : α) (b : β)
    (h : b ∈ decodedPartial (val f) a) : a ∈ A :=
  (encode_mem_codeSupport A a).mp
    (val_source f _ _ ((mem_decodedPartial (val f) a b).mp h))

theorem decoded_target {A : Set α} {B : Set β}
    (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (f : codedCarrier A hA ⟶ codedCarrier B hB) (a : α) (b : β)
    (h : b ∈ decodedPartial (val f) a) : b ∈ B :=
  (encode_mem_codeSupport B b).mp
    (val_target f _ _ ((mem_decodedPartial (val f) a b).mp h))

/-- The numerical presentation applies to every finite power, including power zero. -/
def finitePowerCarrier (n : ℕ) (A : Set (Fin n → ℕ)) (hA : REPred (· ∈ A)) : Carrier :=
  codedCarrier A hA

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers
