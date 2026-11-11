/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeNumeralSpecialization

/-!
# Executable addition and multiplication derivation trees

Addition recurses on its second numeral value, with separate zero and one
cases. Its positive step specializes `AS` and applies modus ponens to the
previous output. Multiplication specializes `MS`, applies it to its previous
output, and then applies the result to the actual addition output at
`(n*k,n)`. Neither recurrence searches for a proof.

The seven addition inputs are packed as
`(((r0,z1),(refl,as)),((Gamma,n),m))`. The ten multiplication inputs are
`((((r0,z1),(refl,as)),((m0,m1),ms)),((Gamma,n),m))`. The six template body
codes are the fixed computable literals in `NativeNumeralSeeds`.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeNumeralArithmetic

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeEqualityTransport
open FailureOfComposition.NativeFamilyExtraction

def addOneCode (z1 refl Γ n : ℕ) : ℕ :=
  if n = 0 then z1 else
    specializeCtx Γ reflBodyCode (addTermCode (numeralTermCode n) Arithmetic.one) refl

def addPositiveCode (as Γ n k ih : ℕ) : ℕ :=
  applyCtxCode Γ (instance3Code asBodyCode n k (n + k))
    (specialize3Code asBodyCode Γ as n k (n + k)) ih

def addCtx (r0 z1 refl as Γ n : ℕ) : ℕ → ℕ
  | 0 => specializeCtx Γ r0BodyCode (numeralTermCode n) r0
  | k + 1 => if k = 0 then addOneCode z1 refl Γ n
      else addPositiveCode as Γ n k (addCtx r0 z1 refl as Γ n k)

def mulPositiveCode (r0 z1 refl as ms Γ n k ih : ℕ) : ℕ :=
  let c := instance4Code msBodyCode n k (n * k) (n * k + n)
  let d := specialize4Code msBodyCode Γ ms n k (n * k) (n * k + n)
  let e := applyCtxCode Γ c d ih
  applyCtxCode Γ (consequentCode c) e (addCtx r0 z1 refl as Γ (n * k) n)

def mulCtx (r0 z1 refl as m0 m1 ms Γ n : ℕ) : ℕ → ℕ
  | 0 => specializeCtx Γ m0BodyCode (numeralTermCode n) m0
  | k + 1 => if k = 0 then specializeCtx Γ m1BodyCode (numeralTermCode n) m1
      else mulPositiveCode r0 z1 refl as ms Γ n k (mulCtx r0 z1 refl as m0 m1 ms Γ n k)

abbrev Seeds4 (X : Type*) := (X × X) × (X × X)
abbrev Seeds7 (X : Type*) := Seeds4 X × ((X × X) × X)
abbrev AddArgs := Seeds4 ℕ × ((ℕ × ℕ) × ℕ)
abbrev MulArgs := Seeds7 ℕ × ((ℕ × ℕ) × ℕ)

def addCtxPacked (u : AddArgs) : ℕ :=
  addCtx u.1.1.1 u.1.1.2 u.1.2.1 u.1.2.2 u.2.1.1 u.2.1.2 u.2.2

def mulCtxPacked (u : MulArgs) : ℕ :=
  mulCtx u.1.1.1.1 u.1.1.1.2 u.1.1.2.1 u.1.1.2.2
    u.1.2.1.1 u.1.2.1.2 u.1.2.2 u.2.1.1 u.2.1.2 u.2.2

theorem addCtx_zero (r0 z1 refl as Γ n : ℕ) :
    addCtx r0 z1 refl as Γ n 0 = specializeCtx Γ r0BodyCode (numeralTermCode n) r0 := rfl

theorem addCtx_one (r0 z1 refl as Γ n : ℕ) :
    addCtx r0 z1 refl as Γ n 1 = addOneCode z1 refl Γ n := by simp [addCtx]

theorem addCtx_succ (r0 z1 refl as Γ n k : ℕ) (hk : 0 < k) :
    addCtx r0 z1 refl as Γ n (k + 1) =
      addPositiveCode as Γ n k (addCtx r0 z1 refl as Γ n k) := by
  simp [addCtx, Nat.ne_of_gt hk]

theorem mulCtx_zero (r0 z1 refl as m0 m1 ms Γ n : ℕ) :
    mulCtx r0 z1 refl as m0 m1 ms Γ n 0 =
      specializeCtx Γ m0BodyCode (numeralTermCode n) m0 := rfl

theorem mulCtx_one (r0 z1 refl as m0 m1 ms Γ n : ℕ) :
    mulCtx r0 z1 refl as m0 m1 ms Γ n 1 =
      specializeCtx Γ m1BodyCode (numeralTermCode n) m1 := by simp [mulCtx]

theorem mulCtx_succ (r0 z1 refl as m0 m1 ms Γ n k : ℕ) (hk : 0 < k) :
    mulCtx r0 z1 refl as m0 m1 ms Γ n (k + 1) =
      mulPositiveCode r0 z1 refl as ms Γ n k (mulCtx r0 z1 refl as m0 m1 ms Γ n k) := by
  simp [mulCtx, Nat.ne_of_gt hk]

end FailureOfComposition.NativeNumeralArithmetic
