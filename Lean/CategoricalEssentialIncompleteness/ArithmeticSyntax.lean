/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalEnumeration
public import Foundation.FirstOrder.Arithmetic.Basic.Misc
public import Foundation.FirstOrder.Syntax.Classical.PrimrecCoding

/-!
# Arithmetic syntax in the numerical category

Sentence codes are the range of the existing `Encodable.encode` function.
Canonical decoding uses `Encodable.decode₂`, which checks that re-encoding the
decoded formula recovers its input. Thus a noncanonical input is rejected even
when the underlying decoder returns a formula.

The canonical sentence codes form an infinite recursive numerical object.
Its increasing enumeration and rank function induce a computable bijection
between natural numbers and arithmetic sentences. Unary formulas are decoded
with the same syntax encoding, with falsity assigned to invalid codes.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open Encodable FFL FFL.FirstOrder

namespace CategoricalEssentialIncompleteness
namespace ArithmeticSyntax

/-- The canonical codes of arithmetic sentences under the syntax encoding. -/
def validSentenceCodes : Set ℕ := Set.range (encode : ArithmeticSentence → ℕ)

theorem validSentenceCodes_primrec : PrimrecPred (· ∈ validSentenceCodes) :=
  Primcodable.mem_range_encode

theorem validSentenceCodes_recursive : ComputablePred (· ∈ validSentenceCodes) :=
  validSentenceCodes_primrec.computablePred

theorem mem_validSentenceCodes_iff (a : ℕ) :
    a ∈ validSentenceCodes ↔ decode₂ ArithmeticSentence a ≠ none :=
  decode₂_ne_none_iff.symm

private def sentenceSequence : ℕ → ArithmeticSentence
  | 0 => Semiformula.verum
  | n + 1 => Semiformula.and (sentenceSequence n) Semiformula.verum

private theorem sentenceSequence_injective : Function.Injective sentenceSequence := by
  intro m
  induction m with
  | zero =>
    intro n h
    cases n with
    | zero => rfl
    | succ n => cases h
  | succ m ih =>
    intro n h
    cases n with
    | zero => cases h
    | succ n => exact congrArg Nat.succ (ih (Semiformula.and.inj h).1)

theorem validSentenceCodes_infinite : validSentenceCodes.Infinite := by
  apply (Set.infinite_range_of_injective
    (encode_injective.comp sentenceSequence_injective)).mono
  rintro a ⟨n, rfl⟩
  exact ⟨sentenceSequence n, rfl⟩

/-- The numerical object of canonical sentence codes. -/
def sentenceCodes : Numerical where
  carrier := validSentenceCodes
  recursive := validSentenceCodes_recursive
  infinite := validSentenceCodes_infinite

/-- The increasing enumeration of canonical sentence codes. -/
def sentenceCodeEnumeration : ℕ → ℕ := Numerical.enumerate sentenceCodes

/-- The number of canonical sentence codes strictly below the given code. -/
def sentenceCodeRank : ℕ → ℕ := Numerical.rank sentenceCodes

theorem sentenceCodeEnumeration_computable : Computable sentenceCodeEnumeration :=
  Numerical.enumerate_computable sentenceCodes

theorem sentenceCodeRank_computable : Computable sentenceCodeRank :=
  Numerical.rank_computable sentenceCodes

theorem sentenceCodeEnumeration_mem (b : ℕ) :
    sentenceCodeEnumeration b ∈ validSentenceCodes :=
  Numerical.enumerate_mem sentenceCodes b

theorem sentenceCodeEnumeration_injective : Function.Injective sentenceCodeEnumeration :=
  Numerical.enumerate_injective sentenceCodes

@[simp] theorem sentenceCodeRank_enumeration (b : ℕ) :
    sentenceCodeRank (sentenceCodeEnumeration b) = b :=
  Numerical.rank_enumerate sentenceCodes b

theorem sentenceCodeEnumeration_rank {a : ℕ} (ha : a ∈ validSentenceCodes) :
    sentenceCodeEnumeration (sentenceCodeRank a) = a :=
  Numerical.enumerate_rank sentenceCodes ha

/-- Decode the increasing enumeration into arithmetic sentences. -/
def sentenceEnumeration (b : ℕ) : ArithmeticSentence :=
  (decode₂ ArithmeticSentence (sentenceCodeEnumeration b)).getD ⊥

theorem sentenceEnumeration_computable : Computable sentenceEnumeration :=
  Computable.option_getD
    (Primrec.decode₂.to_comp.comp sentenceCodeEnumeration_computable) (Computable.const _)

@[simp] theorem encode_sentenceEnumeration (b : ℕ) :
    encode (sentenceEnumeration b) = sentenceCodeEnumeration b := by
  obtain ⟨φ, hφ⟩ := sentenceCodeEnumeration_mem b
  simp only [sentenceEnumeration, ← hφ, decode₂_encode, Option.getD_some]

/-- The index of a sentence in the increasing enumeration of canonical codes. -/
def sentenceIndex (φ : ArithmeticSentence) : ℕ := sentenceCodeRank (encode φ)

theorem sentenceIndex_computable : Computable sentenceIndex :=
  sentenceCodeRank_computable.comp Computable.encode

@[simp] theorem sentenceIndex_enumeration (b : ℕ) :
    sentenceIndex (sentenceEnumeration b) = b := by
  simp only [sentenceIndex, encode_sentenceEnumeration, sentenceCodeRank_enumeration]

@[simp] theorem sentenceEnumeration_index (φ : ArithmeticSentence) :
    sentenceEnumeration (sentenceIndex φ) = φ := by
  apply encode_injective
  rw [encode_sentenceEnumeration]
  exact sentenceCodeEnumeration_rank ⟨φ, rfl⟩

/-- The computable enumeration and indexing maps are inverse bijections. -/
def sentenceEquiv : ℕ ≃ ArithmeticSentence where
  toFun := sentenceEnumeration
  invFun := sentenceIndex
  left_inv := sentenceIndex_enumeration
  right_inv := sentenceEnumeration_index

theorem sentenceEnumeration_bijective : Function.Bijective sentenceEnumeration :=
  sentenceEquiv.bijective

/-- Decode a unary arithmetic formula, assigning falsity to noncanonical codes. -/
def unaryFormula (a : ℕ) : ArithmeticSemiformula Empty 1 :=
  (decode₂ (ArithmeticSemiformula Empty 1) a).getD ⊥

theorem unaryFormula_primrec : Primrec unaryFormula :=
  Primrec.option_getD.comp Primrec.decode₂ (Primrec.const _)

theorem unaryFormula_computable : Computable unaryFormula := unaryFormula_primrec.to_comp

@[simp] theorem unaryFormula_encode (φ : ArithmeticSemiformula Empty 1) :
    unaryFormula (encode φ) = φ := by
  simp only [unaryFormula, decode₂_encode, Option.getD_some]

theorem unaryFormula_of_invalid {a : ℕ}
    (ha : a ∉ Set.range (encode : ArithmeticSemiformula Empty 1 → ℕ)) :
    unaryFormula a = ⊥ := by
  have h : decode₂ (ArithmeticSemiformula Empty 1) a = none := by
    by_contra h
    exact ha (decode₂_ne_none_iff.mp h)
  simp only [unaryFormula, h, Option.getD_none]

theorem encode_unaryFormula_of_valid {a : ℕ}
    (ha : a ∈ Set.range (encode : ArithmeticSemiformula Empty 1 → ℕ)) :
    encode (unaryFormula a) = a := by
  obtain ⟨φ, rfl⟩ := ha
  rw [unaryFormula_encode]

end ArithmeticSyntax
end CategoricalEssentialIncompleteness
