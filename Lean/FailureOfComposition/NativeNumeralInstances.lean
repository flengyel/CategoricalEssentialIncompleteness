/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeNumeralSpecialization
import FailureOfComposition.NativeFamilyPreservation

/-!
# Literal instances of the arithmetic seeds

Specializing in operational order reverses the coordinate vector of a seed
matrix. The identities below are identities of formula codes in the model,
not merely equivalences of their meanings. The accompanying derivation
lemmas follow the actual chain of context-preserving specializations.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeNumeralArithmetic

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeEqualityTransport
open FailureOfComposition.NativeSubstitution
open FailureOfComposition.NativeFamilyExtraction

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

private theorem first3 (phi : Bootstrapping.Semiformula V ℒₒᵣ 3) (x : V) :
    subst1Value (Arithmetic.numeral x) (^∀ (^∀ phi.val)) =
      ^∀ (^∀ (phi.subst ![Bootstrapping.Semiterm.bvar (0 : Fin 2),
        Bootstrapping.Semiterm.bvar 1, typedNumeral x]).val) := by
  rw [show (^∀ (^∀ phi.val) : V) = (∀¹ ∀¹ phi : Bootstrapping.Semiformula V ℒₒᵣ 1).val from rfl,
    subst1Value_typedNumeral]
  simp only [Bootstrapping.Semiformula.substs_all, Bootstrapping.Semiformula.val_all]
  congr 3
  apply congrArg (fun w : Bootstrapping.SemitermVec V ℒₒᵣ 3 2 => phi.subst w)
  funext i
  fin_cases i <;> simp [SemitermVec.q, toNumVec]

private theorem second3 (phi : Bootstrapping.Semiformula V ℒₒᵣ 3) (x y : V) :
    subst1Value (Arithmetic.numeral y)
      (^∀ (phi.subst ![Bootstrapping.Semiterm.bvar (0 : Fin 2),
        Bootstrapping.Semiterm.bvar 1, typedNumeral x]).val) =
      ^∀ (phi.subst ![Bootstrapping.Semiterm.bvar (0 : Fin 1),
        typedNumeral y, typedNumeral x]).val := by
  let a : Bootstrapping.Semiformula V ℒₒᵣ 2 :=
    phi.subst ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.bvar 1, typedNumeral x]
  rw [show (^∀ a.val : V) = (∀¹ a : Bootstrapping.Semiformula V ℒₒᵣ 1).val from rfl,
    subst1Value_typedNumeral]
  simp only [Bootstrapping.Semiformula.substs_all, Bootstrapping.Semiformula.val_all]
  congr 1
  dsimp only [a]
  rw [Bootstrapping.Semiformula.substs_substs]
  congr 2
  funext i
  fin_cases i <;> simp [SemitermVec.q, toNumVec]

private theorem third3 (phi : Bootstrapping.Semiformula V ℒₒᵣ 3) (x y z : V) :
    subst1Value (Arithmetic.numeral z)
      (phi.subst ![Bootstrapping.Semiterm.bvar (0 : Fin 1), typedNumeral y, typedNumeral x]).val =
      (phi.subst (toNumVec (k := 0) ![z, y, x])).val := by
  rw [subst1Value_typedNumeral, Bootstrapping.Semiformula.substs_substs]
  congr 2
  funext i
  fin_cases i <;> simp [toNumVec]

theorem instance3_typed (phi : Bootstrapping.Semiformula V ℒₒᵣ 3) (x y z : V) :
    instance3Value (^∀ (^∀ phi.val)) x y z = (phi.subst (toNumVec (k := 0) ![z, y, x])).val := by
  simp only [instance3Value, nextBodyValue, first3, allBodyValue_all, second3, third3]

theorem derivationOf_specialize3 (S : ArithmeticTheory) [S.Δ₁]
    (phi : Bootstrapping.Semiformula V ℒₒᵣ 3) {Γ seed x y z : V}
    (hs : DerivationOf S seed (insert (^∀ (^∀ (^∀ phi.val))) Γ)) :
    DerivationOf S (specialize3Value (^∀ (^∀ phi.val)) Γ seed x y z)
      (insert (instance3Value (^∀ (^∀ phi.val)) x y z) Γ) := by
  have h₁ := derivationOf_specializeNumeral S (u := x) hs
  rw [first3] at h₁
  have h₂ := derivationOf_specializeNumeral S (u := y) h₁
  rw [second3] at h₂
  have h₃ := derivationOf_specializeNumeral S (u := z) h₂
  simpa only [specialize3Value, instance3Value, nextBodyValue,
    first3, allBodyValue_all, second3] using h₃

private theorem first4 (phi : Bootstrapping.Semiformula V ℒₒᵣ 4) (x : V) :
    subst1Value (Arithmetic.numeral x) (^∀ (^∀ (^∀ phi.val))) =
      ^∀ (^∀ (^∀ (phi.subst ![Bootstrapping.Semiterm.bvar (0 : Fin 3),
        Bootstrapping.Semiterm.bvar 1, Bootstrapping.Semiterm.bvar 2, typedNumeral x]).val)) := by
  rw [show (^∀ (^∀ (^∀ phi.val)) : V) =
    (∀¹ ∀¹ ∀¹ phi : Bootstrapping.Semiformula V ℒₒᵣ 1).val from rfl, subst1Value_typedNumeral]
  simp only [Bootstrapping.Semiformula.substs_all, Bootstrapping.Semiformula.val_all]
  congr 4
  apply congrArg (fun w : Bootstrapping.SemitermVec V ℒₒᵣ 4 3 => phi.subst w)
  funext i
  fin_cases i <;> simp [SemitermVec.q, toNumVec]

theorem instance4_typed (phi : Bootstrapping.Semiformula V ℒₒᵣ 4) (x y z w : V) :
    instance4Value (^∀ (^∀ (^∀ phi.val))) x y z w =
      (phi.subst (toNumVec (k := 0) ![w, z, y, x])).val := by
  simp only [instance4Value, nextBodyValue, first4, allBodyValue_all, instance3_typed]
  rw [Bootstrapping.Semiformula.substs_substs]
  congr 2
  funext i
  fin_cases i <;> simp [toNumVec]

theorem derivationOf_specialize4 (S : ArithmeticTheory) [S.Δ₁]
    (phi : Bootstrapping.Semiformula V ℒₒᵣ 4) {Γ seed x y z w : V}
    (hs : DerivationOf S seed (insert (^∀ (^∀ (^∀ (^∀ phi.val)))) Γ)) :
    DerivationOf S (specialize4Value (^∀ (^∀ (^∀ phi.val))) Γ seed x y z w)
      (insert (instance4Value (^∀ (^∀ (^∀ phi.val))) x y z w) Γ) := by
  have h₁ := derivationOf_specializeNumeral S (u := x) hs
  rw [first4] at h₁
  have h₂ := derivationOf_specialize3 S _ (x := y) (y := z) (z := w) h₁
  simpa only [specialize4Value, instance4Value, nextBodyValue, first4, allBodyValue_all] using h₂

theorem asBody_cast : (asBodyCode : V) = ^∀ (^∀ (⌜asMatrix⌝ : V)) := by
  rw [asBodyCode, ← Sentence.quote_eq_encode]
  simp only [asBody, all_quote]

theorem msBody_cast : (msBodyCode : V) = ^∀ (^∀ (^∀ (⌜msMatrix⌝ : V))) := by
  rw [msBodyCode, ← Sentence.quote_eq_encode]
  simp only [msBody, all_quote]

theorem asSentence_literal : (⌜asSentence⌝ : V) =
    ^∀ (^∀ (^∀ (⌜asMatrix⌝ : Bootstrapping.Semiformula V ℒₒᵣ 3).val)) := by
  rw [asSentence, asBody, all_quote, all_quote, all_quote, Sentence.quote_eq]

theorem msSentence_literal : (⌜msSentence⌝ : V) =
    ^∀ (^∀ (^∀ (^∀ (⌜msMatrix⌝ : Bootstrapping.Semiformula V ℒₒᵣ 4).val))) := by
  rw [msSentence, msBody, all_quote, all_quote, all_quote, all_quote, Sentence.quote_eq]

theorem as_instance (n k t : V) :
    instance3Value (asBodyCode : V) n k t =
      imp ℒₒᵣ (qqEQ (qqAdd (Arithmetic.numeral n) (Arithmetic.numeral k)) (Arithmetic.numeral t))
        (qqEQ (qqAdd (Arithmetic.numeral n) (qqAdd (Arithmetic.numeral k) (Arithmetic.one : V)))
          (qqAdd (Arithmetic.numeral t) (Arithmetic.one : V))) := by
  rw [asBody_cast, Sentence.quote_eq asMatrix,
    instance3_typed (⌜asMatrix⌝ : Bootstrapping.Semiformula V ℒₒᵣ 3)]
  simp [asMatrix, Sentence.typed_quote_def, toNumVec]

theorem ms_instance (n k t u : V) :
    instance4Value (msBodyCode : V) n k t u =
      imp ℒₒᵣ (qqEQ (qqMul (Arithmetic.numeral n) (Arithmetic.numeral k)) (Arithmetic.numeral t))
        (imp ℒₒᵣ (qqEQ (qqAdd (Arithmetic.numeral t) (Arithmetic.numeral n)) (Arithmetic.numeral u))
          (qqEQ (qqMul (Arithmetic.numeral n) (qqAdd (Arithmetic.numeral k) (Arithmetic.one : V)))
            (Arithmetic.numeral u))) := by
  rw [msBody_cast, Sentence.quote_eq msMatrix,
    instance4_typed (⌜msMatrix⌝ : Bootstrapping.Semiformula V ℒₒᵣ 4)]
  simp [msMatrix, Sentence.typed_quote_def, toNumVec]

theorem r0_instance (n : V) :
    subst1Value (Arithmetic.numeral n) (r0BodyCode : V) = addEq n 0 := by
  rw [r0BodyCode, ← Sentence.quote_eq_encode, Sentence.quote_eq r0Body,
    subst1Value_typedNumeral (⌜r0Body⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1)]
  simp [r0Body, Sentence.typed_quote_def, toNumVec, addEq]

theorem refl_instance (t : Bootstrapping.Semiterm V ℒₒᵣ 0) :
    subst1Value t.val (reflBodyCode : V) = qqEQ t.val t.val := by
  rw [reflBodyCode, ← Sentence.quote_eq_encode,
    subst1Value_eq_substs1 t.isSemiterm (by simp)]
  change ((⌜reflBody⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1).subst ![t]).val = _
  simp [reflBody, Sentence.typed_quote_def]

theorem m0_instance (n : V) :
    subst1Value (Arithmetic.numeral n) (m0BodyCode : V) = mulEq n 0 := by
  rw [m0BodyCode, ← Sentence.quote_eq_encode, Sentence.quote_eq m0Body,
    subst1Value_typedNumeral (⌜m0Body⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1)]
  simp [m0Body, Sentence.typed_quote_def, toNumVec, mulEq]

theorem m1_instance (n : V) :
    subst1Value (Arithmetic.numeral n) (m1BodyCode : V) = mulEq n 1 := by
  rw [m1BodyCode, ← Sentence.quote_eq_encode, Sentence.quote_eq m1Body,
    subst1Value_typedNumeral (⌜m1Body⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1)]
  simp [m1Body, Sentence.typed_quote_def, toNumVec, mulEq]

theorem z1_literal : (⌜z1Sentence⌝ : V) = addEq (0 : V) 1 := by
  change (⌜z1Sentence⌝ : Bootstrapping.Semiformula V ℒₒᵣ 0).val = _
  simp [z1Sentence, Sentence.typed_quote_def, addEq]

theorem as_positive_literal (n k : V) (hk : 0 < k) :
    instance3Value (asBodyCode : V) n k (n + k) = imp ℒₒᵣ (addEq n k) (addEq n (k + 1)) := by
  rw [as_instance]
  have hnk : 0 < n + k := lt_of_lt_of_le hk le_add_self
  simp only [addEq, ← add_assoc, numeral_succ_pos hk, numeral_succ_pos hnk]

theorem ms_positive_literal (n k : V) (hk : 0 < k) :
    instance4Value (msBodyCode : V) n k (n * k) (n * k + n) =
      imp ℒₒᵣ (mulEq n k) (imp ℒₒᵣ (addEq (n * k) n) (mulEq n (k + 1))) := by
  rw [ms_instance]
  simp only [mulEq, addEq, numeral_succ_pos hk, mul_add, mul_one]

end FailureOfComposition.NativeNumeralArithmetic
