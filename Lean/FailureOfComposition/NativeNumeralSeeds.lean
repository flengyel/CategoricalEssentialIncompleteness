/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeNumeralSyntax
public import Foundation.Meta.ClProver

/-!
# Seven fixed arithmetic seeds

These sentences supply the arithmetic content of the proof recurrences.
Their proofs are fixed before any numeral inputs or ambient model are chosen.
The step matrices use reversed de Bruijn coordinates: `(z,y,x)` for addition
and `(w,z,y,x)` for multiplication. Operational specialization proceeds in the
displayed order `x,y,z` or `x,y,z,w`.

The body codes below encode fixed, computable literal formulas. They contain
no theory-dependent proof selection. In particular, the reflexivity seed is
later specialized at the addition **term**, not at a successor of its code.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeNumeralArithmetic

open FFL.FirstOrder.Arithmetic.Bootstrapping

def r0Body : ArithmeticSemisentence 1 := “x. x + 0 = x”
def r0Sentence : ArithmeticSentence := ∀¹ r0Body
def z1Sentence : ArithmeticSentence := “0 + 1 = 1”
def reflBody : ArithmeticSemisentence 1 := “x. x = x”
def reflSentence : ArithmeticSentence := ∀¹ reflBody
def asMatrix : ArithmeticSemisentence 3 := “z y x. x + y = z → x + (y + 1) = z + 1”
def asBody : ArithmeticSemisentence 1 := ∀¹ ∀¹ asMatrix
def asSentence : ArithmeticSentence := ∀¹ asBody
def m0Body : ArithmeticSemisentence 1 := “x. x * 0 = 0”
def m0Sentence : ArithmeticSentence := ∀¹ m0Body
def m1Body : ArithmeticSemisentence 1 := “x. x * 1 = x”
def m1Sentence : ArithmeticSentence := ∀¹ m1Body
def msMatrix : ArithmeticSemisentence 4 :=
  “w z y x. x * y = z → z + x = w → x * (y + 1) = w”
def msBody : ArithmeticSemisentence 1 := ∀¹ ∀¹ ∀¹ msMatrix
def msSentence : ArithmeticSentence := ∀¹ msBody

def r0BodyCode : ℕ := encode r0Body
def reflBodyCode : ℕ := encode reflBody
def asBodyCode : ℕ := encode asBody
def m0BodyCode : ℕ := encode m0Body
def m1BodyCode : ℕ := encode m1Body
def msBodyCode : ℕ := encode msBody

theorem r0_provable : 𝗣𝗔⁻ ⊢ r0Sentence := by
  apply complete.{0}
  intro M _ hM
  simp [r0Sentence, r0Body, models_iff]

theorem z1_provable : 𝗣𝗔⁻ ⊢ z1Sentence := by
  apply complete.{0}
  intro M _ hM
  simp [z1Sentence, models_iff]

theorem refl_provable : 𝗣𝗔⁻ ⊢ reflSentence := by
  apply complete.{0}
  intro M _ hM
  simp [reflSentence, reflBody, models_iff]

theorem as_provable : 𝗣𝗔⁻ ⊢ asSentence := by
  apply complete.{0}
  intro M _ hM
  simp [asSentence, asBody, asMatrix, models_iff, ← add_assoc]

theorem m0_provable : 𝗣𝗔⁻ ⊢ m0Sentence := by
  apply complete.{0}
  intro M _ hM
  simp [m0Sentence, m0Body, models_iff]

theorem m1_provable : 𝗣𝗔⁻ ⊢ m1Sentence := by
  apply complete.{0}
  intro M _ hM
  simp [m1Sentence, m1Body, models_iff]

theorem ms_provable : 𝗣𝗔⁻ ⊢ msSentence := by
  apply complete.{0}
  intro M _ hM
  simp [msSentence, msBody, msMatrix, models_iff, mul_add]

section Internal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem bodyCode_quote {n : ℕ} (phi : ArithmeticSemisentence n) :
    (ORingStructure.numeral (encode phi) : V) = (⌜phi⌝ : V) := by
  rw [numeral_eq_natCast_app, Sentence.quote_eq_encode]

theorem all_quote {n : ℕ} (phi : ArithmeticSemisentence (n + 1)) :
    (⌜∀¹ phi⌝ : V) = ^∀ (⌜phi⌝ : V) := by
  simp [Sentence.quote_def]

end Internal

end FailureOfComposition.NativeNumeralArithmetic
