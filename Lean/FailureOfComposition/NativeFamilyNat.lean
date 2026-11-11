/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeFamilyConstructor

/-!
# Full-domain numerical comparison for family extraction

These equalities have no well-formedness or proof-acceptance premises.
Malformed numerical inputs retain the behavior fixed by the constructor.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeFamilyExtraction

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeContextMP
open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeSubstitution
open FailureOfComposition.NativeEqualityTransport

private theorem pi₁_nat (a : ℕ) : (π₁ a : ℕ) = a.unpair.1 := by
  calc
    (π₁ a : ℕ) = π₁ (Nat.pair a.unpair.1 a.unpair.2) := by rw [Nat.pair_unpair]
    _ = a.unpair.1 := by rw [← nat_pair_eq]; simp

private theorem pi₂_nat (a : ℕ) : (π₂ a : ℕ) = a.unpair.2 := by
  calc
    (π₂ a : ℕ) = π₂ (Nat.pair a.unpair.1 a.unpair.2) := by rw [Nat.pair_unpair]
    _ = a.unpair.2 := by rw [← nat_pair_eq]; simp

theorem allBodyValue_nat (a : ℕ) : sndIdx a = allBodyCode a := by
  cases a with
  | zero => simp [sndIdx, allBodyCode, pi₂_zero]
  | succ n => simpa [sndIdx, allBodyCode] using pi₂_nat n

theorem consequentValue_nat (a : ℕ) : consequentValue a = consequentCode a := by
  rw [consequentValue, allBodyValue_nat, pi₂_nat]
  rfl

theorem antecedentValue_nat (a : ℕ) : antecedentValue a = antecedentCode a := by
  have hn (x : ℕ) : guardedNegValue x = formulaNegTotalCode x := by
    by_cases hx : IsFormula ℒₒᵣ x
    · rw [guardedNegValue_eq_neg hx, formulaNegTotalCode_eq_neg hx]
    · simp [guardedNegValue, formulaNegTotalCode_eq_zero hx, hx]
  rw [antecedentValue, hn, allBodyValue_nat, pi₁_nat]
  rfl

theorem applyCtxValue_nat (Γ c e p : ℕ) : applyCtxValue Γ c e p = applyCtxCode Γ c e p := by
  rw [applyCtxValue, antecedentValue_nat, consequentValue_nat, mpCtxValue_nat]
  rfl

theorem extractValue_nat (body seed Γ e m pH pK u y r : ℕ) :
    extractValue body seed Γ e m pH pK u y r = extractCtx body seed Γ e m pH pK u y r := by
  simp only [extractValue, numeral_eq_natCast_app, natCast_nat,
    numeralTermCodeValue_nat, subst1Value_nat, allBodyValue_nat,
    consequentValue_nat, specializeCtxValue_nat, applyCtxValue_nat]
  simp only [extractCtx]

theorem extractGraph_nat_iff (body o seed Γ e m pH pK u y r : ℕ) :
    (extractGraph body).val.Evalb ![o, seed, Γ, e, m, pH, pK, u, y, r] ↔
      o = extractCtx body seed Γ e m pH pK u y r := by
  rw [extractGraph_iff, extractValue_nat]

end FailureOfComposition.NativeFamilyExtraction
