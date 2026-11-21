/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ExponentialPairing
public import Mathlib.Computability.Primrec.Basic

/-! # A primitive-recursion certificate for the product pairing -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace CategoricalEssentialIncompleteness.V46.ExponentialPairing

theorem code_nat (a b : ℕ) : code a b = Nat.pred (2 ^ a * (2 * b + 1)) := by
  have h₁ : code a b + 1 = 2 ^ a * (2 * b + 1) := by
    rw [code_add_one, Arithmetic.exp_nat_eq_two_pow]
    rfl
  have hp : 0 < 2 ^ a * (2 * b + 1) := by positivity
  have h₂ : Nat.pred (2 ^ a * (2 * b + 1)) + 1 = 2 ^ a * (2 * b + 1) :=
    Nat.succ_pred_eq_of_pos hp
  exact Nat.add_right_cancel (h₁.trans h₂.symm)

theorem code_primrec : Primrec₂ (code (M := ℕ)) := by
  have hpow : Primrec₂ (fun a b : ℕ => a ^ b) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have h : Primrec (fun p : ℕ × ℕ => Nat.pred (2 ^ p.1 * (2 * p.2 + 1))) :=
    Primrec.pred.comp (Primrec.nat_mul.comp
      (hpow.comp (Primrec.const 2) Primrec.fst)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
        (Primrec.const 1)))
  exact h.of_eq (fun p => (code_nat p.1 p.2).symm)

end CategoricalEssentialIncompleteness.V46.ExponentialPairing
