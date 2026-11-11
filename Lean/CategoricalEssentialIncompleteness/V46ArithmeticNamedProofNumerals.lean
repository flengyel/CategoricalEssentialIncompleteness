/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedFormulaTranslation
public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic
public import Foundation.FirstOrder.LK.Completeness

/-! # Source proof numerals matching the literal named recurrence

Foundation's numeral one is its constant one. The literal named numeral
one is zero plus one. Expanded source numerals preserve this distinction
and have an exact syntactic translation; their equality to Foundation's
numerals is a separate actual PA theorem.
-/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedProofNumerals
open NamedArithmeticSignature ArithmeticNamedTranslation

/-- The source term recurrence is deliberately expanded at one. -/
def expandedNumeral : ℕ → ArithmeticSemiterm Empty 0
  | 0 => .func .zero Fin.elim0
  | n + 1 => .func .add ![expandedNumeral n,.func .one Fin.elim0]

@[simp] theorem expandedNumeral_zero : expandedNumeral 0 = .func .zero Fin.elim0 := rfl
@[simp] theorem expandedNumeral_succ (n : ℕ) :
    expandedNumeral (n+1) = .func .add ![expandedNumeral n,.func .one Fin.elim0] := rfl

/-- This is syntactic equality, with every function symbol and ordered
child retained. It does not compare terms by their evaluated values. -/
theorem translate_expandedNumeral (names : Fin 0 → ℕ) (n : ℕ) :
    translateTerm names (expandedNumeral n) = NamedArithmeticSignature.numeral n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change NamedArithmeticSignature.add (translateTerm names (expandedNumeral n))
        NamedArithmeticSignature.one =
          NamedArithmeticSignature.add (NamedArithmeticSignature.numeral n) NamedArithmeticSignature.one
      exact congrArg (fun r => NamedArithmeticSignature.add r NamedArithmeticSignature.one) ih

/-- The source standard numeral one translates to the literal constant
one, so it is not silently identified with the expanded recurrence. -/
theorem translate_standard_one (names : Fin 0 → ℕ) :
    translateTerm names (↑(1 : ℕ) : ArithmeticSemiterm Empty 0) = NamedArithmeticSignature.one := rfl

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Model evaluation is used only to construct a proof in the source
PA calculus through its proved completeness theorem. -/
theorem expandedNumeral_value (n : ℕ) :
    (expandedNumeral n).val (s := Arithmetic.standardModel M) ![] Empty.elim = (n : M) := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  induction n with
  | zero => rfl
  | succ n ih =>
      change (expandedNumeral n).val (s := Arithmetic.standardModel M) ![] Empty.elim + 1 = ((n+1 : ℕ) : M)
      rw [ih,Nat.cast_add,Nat.cast_one]

end Models

/-- An actual source PA proof compares the two numeral conventions.
This theorem alone is not a native proof translation. -/
theorem expandedNumeral_eq_standard_PA (n : ℕ) :
    𝗣𝗔 ⊢ (Semiformula.rel .eq ![expandedNumeral n,(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simpa [models_iff,Arithmetic.standardModel,numeral_eq_natCast] using (expandedNumeral_value (M := M) n)


/-- PA identifies the two closed instances using the proved term values;
this is a source proof equivalence, not equality of their syntax. -/
theorem expanded_instance_equivalence_PA (φ : ArithmeticSemisentence 1) (n : ℕ) :
    𝗣𝗔 ⊢ ((φ/[expandedNumeral n] : ArithmeticSentence) 🡘
      (φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simp [models_iff,expandedNumeral_value,numeral_eq_natCast]

/-- A canonical numeral proof supplies the expanded instance needed by
the literal named numeral-substitution algorithm. -/
theorem expanded_instance_PA (φ : ArithmeticSemisentence 1) (n : ℕ)
    (h : 𝗣𝗔 ⊢ (φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) :
    𝗣𝗔 ⊢ (φ/[expandedNumeral n] : ArithmeticSentence) :=
  (K_right (expanded_instance_equivalence_PA φ n)) ⨀ h

/-- The same proved comparison transports a refutation. -/
theorem expanded_instance_refutation_PA (φ : ArithmeticSemisentence 1) (n : ℕ)
    (h : 𝗣𝗔 ⊢ ∼(φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) :
    𝗣𝗔 ⊢ ∼(φ/[expandedNumeral n] : ArithmeticSentence) :=
  (K_right (ENN_of_E (expanded_instance_equivalence_PA φ n))) ⨀ h

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedProofNumerals
