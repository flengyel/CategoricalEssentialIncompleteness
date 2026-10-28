/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeNumeralComparisonSyntax
import FailureOfComposition.NativeNumeralSeeds

/-!
# Four comparison seeds

The eight comparison seeds consist of the four addition seeds followed by the
four sentences below. Matrices have reversed de Bruijn coordinates. Their
operational specialization orders are `x,y,z,w`, `x,y,z`, and `x,y`.
Both disequality seeds conclude `x ≠ y`; the reverse seed has premise `y < x`.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeNumeralComparison

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open FailureOfComposition.NativeNumeralArithmetic
open FailureOfComposition.NativeEqualityTransport

open FFL.Entailment

def ltBridgeMatrix : ArithmeticSemisentence 4 :=
  “w z y x. y + x = z → z + 1 = w → x < w”
def ltBridgeBody : ArithmeticSemisentence 1 := ∀¹ ∀¹ ∀¹ ltBridgeMatrix
def ltBridgeSentence : ArithmeticSentence := ∀¹ ltBridgeBody

def nltBridgeMatrix : ArithmeticSemisentence 3 := “z y x. y + x = z → ¬(z < x)”
def nltBridgeBody : ArithmeticSemisentence 1 := ∀¹ ∀¹ nltBridgeMatrix
def nltBridgeSentence : ArithmeticSentence := ∀¹ nltBridgeBody

def neForwardMatrix : ArithmeticSemisentence 2 := “y x. x < y → x ≠ y”
def neForwardBody : ArithmeticSemisentence 1 := ∀¹ neForwardMatrix
def neForwardSentence : ArithmeticSentence := ∀¹ neForwardBody

def neReverseMatrix : ArithmeticSemisentence 2 := “y x. y < x → x ≠ y”
def neReverseBody : ArithmeticSemisentence 1 := ∀¹ neReverseMatrix
def neReverseSentence : ArithmeticSentence := ∀¹ neReverseBody

def ltBridgeBodyCode : ℕ := encode ltBridgeBody
def nltBridgeBodyCode : ℕ := encode nltBridgeBody
def neForwardBodyCode : ℕ := encode neForwardBody
def neReverseBodyCode : ℕ := encode neReverseBody

theorem ltBridge_provable : 𝗣𝗔⁻ ⊢ ltBridgeSentence := by
  apply complete.{0}
  intro M _ hM
  have h : ∀ (x y z w : M), y + x = z → z + 1 = w → x < w := by
    intro x y z w hz hw
    subst z w
    exact lt_of_le_of_lt le_add_self (lt_add_one (y + x))
  simpa [ltBridgeSentence, ltBridgeBody, ltBridgeMatrix, models_iff] using h

theorem nltBridge_provable : 𝗣𝗔⁻ ⊢ nltBridgeSentence := by
  apply complete.{0}
  intro M _ hM
  simp [nltBridgeSentence, nltBridgeBody, nltBridgeMatrix, models_iff]

theorem neForward_provable : 𝗣𝗔⁻ ⊢ neForwardSentence := by
  apply complete.{0}
  intro M _ hM
  have h : ∀ (x y : M), x < y → x ≠ y := fun _ _ h => ne_of_lt h
  simpa [neForwardSentence, neForwardBody, neForwardMatrix, models_iff] using h

theorem neReverse_provable : 𝗣𝗔⁻ ⊢ neReverseSentence := by
  apply complete.{0}
  intro M _ hM
  have h : ∀ (x y : M), y < x → x ≠ y := fun _ _ h => ne_of_gt h
  simpa [neReverseSentence, neReverseBody, neReverseMatrix, models_iff] using h

end FailureOfComposition.NativeNumeralComparison
