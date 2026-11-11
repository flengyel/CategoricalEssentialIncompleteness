/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeNumeralAdditionGraph

/-!
# Structural internal recurrence for multiplication proofs

The positive step includes a call to `addGraph` on `(n*k,n)`, with the same
addition seeds and context. The blueprint has nine parameters
`(r0,z1,refl,as,m0,m1,ms,Gamma,n)`. Its public graph has output first and the
ten varying inputs afterward. It describes a numerical operation, not a
predicate asserting existence of an arbitrary proof.
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

noncomputable def mulPositiveGraph : 𝚺₁.Semisentence 10 := .mkSigma
  “o r0 z1 refl as ms Γ n k ih.
    ∃ c, !instance4Graph c ↑msBodyCode n k (n * k) (n * k + n) ∧
    ∃ d, !specialize4Graph d ↑msBodyCode Γ ms n k (n * k) (n * k + n) ∧
    ∃ e, !applyCtxGraph e Γ c d ih ∧
    ∃ c1, !consequentGraph c1 c ∧
    ∃ a, !addGraph a r0 z1 refl as Γ (n * k) n ∧ !applyCtxGraph o Γ c1 e a”

namespace MulRec

noncomputable def blueprint : PR.Blueprint 9 where
  zero := .mkSigma “o r0 z1 refl as m0 m1 ms Γ n.
    ∃ nn, !numeralTermCodeGraph nn n ∧ !specializeCtxGraph o Γ ↑m0BodyCode nn m0”
  succ := .mkSigma “o ih k r0 z1 refl as m0 m1 ms Γ n.
    (k = 0 ∧ ∃ nn, !numeralTermCodeGraph nn n ∧ !specializeCtxGraph o Γ ↑m1BodyCode nn m1) ∨
    (k ≠ 0 ∧ !mulPositiveGraph o r0 z1 refl as ms Γ n k ih)”

end MulRec

section Internal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def mulPositiveValue (r0 z1 refl as ms Γ n k ih : V) : V :=
  let c := instance4Value (msBodyCode : V) n k (n * k) (n * k + n)
  let d := specialize4Value (msBodyCode : V) Γ ms n k (n * k) (n * k + n)
  let e := applyCtxValue Γ c d ih
  applyCtxValue Γ (consequentValue c) e (addValue r0 z1 refl as Γ (n * k) n)

private theorem consequentGraph_eval (v : Fin 2 → V) :
    consequentGraph.val.Evalb v ↔ v 0 = consequentValue (v 1) := by
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  exact consequentGraph_iff _ _

@[simp] theorem mulPositiveGraph_eval (v : Fin 10 → V) :
    mulPositiveGraph.val.Evalb v ↔
      v 0 = mulPositiveValue (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) := by
  simp [mulPositiveGraph, mulPositiveValue, consequentGraph_eval,
    Tarski.Structure.numeral_eq_numeral, numeral_eq_natCast_app]

namespace MulRec

noncomputable def construction : PR.Construction V blueprint where
  zero v := specializeCtxValue (v 7) (m0BodyCode : V) (Arithmetic.numeral (v 8)) (v 4)
  succ v k ih := if k = 0 then
    specializeCtxValue (v 7) (m1BodyCode : V) (Arithmetic.numeral (v 8)) (v 5)
    else mulPositiveValue (v 0) (v 1) (v 2) (v 3) (v 6) (v 7) (v 8) k ih
  zero_defined := .mk fun v => by
    simp [blueprint, numeralTermCodeGraph_iff, Tarski.Structure.numeral_eq_numeral,
      numeral_eq_natCast_app]
  succ_defined := .mk fun v => by
    by_cases hk : v 2 = 0 <;>
      simp [blueprint, hk, numeralTermCodeGraph_iff, Tarski.Structure.numeral_eq_numeral,
        numeral_eq_natCast_app]

end MulRec

noncomputable def mulValue (r0 z1 refl as m0 m1 ms Γ n m : V) : V :=
  MulRec.construction.result ![r0, z1, refl, as, m0, m1, ms, Γ, n] m

noncomputable def mulGraph : 𝚺₁.Semisentence 11 :=
  MulRec.blueprint.resultDef.rew (Rew.subst ![#0, #10, #1, #2, #3, #4, #5, #6, #7, #8, #9])

theorem mulGraph_iff (o r0 z1 refl as m0 m1 ms Γ n m : V) :
    mulGraph.val.Evalb ![o, r0, z1, refl, as, m0, m1, ms, Γ, n, m] ↔
      o = mulValue r0 z1 refl as m0 m1 ms Γ n m := by
  simpa [mulGraph, mulValue, Matrix.comp_vecCons''] using
    (MulRec.construction (V := V)).result_defined_iff ![o, m, r0, z1, refl, as, m0, m1, ms, Γ, n]

@[simp] theorem mulGraph_eval (v : Fin 11 → V) :
    mulGraph.val.Evalb v ↔
      v 0 = mulValue (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) := by
  have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  exact mulGraph_iff _ _ _ _ _ _ _ _ _ _ _

instance mulValue_defined : 𝚺₁.DefinedFunction
    (fun v : Fin 10 → V =>
      mulValue (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) mulGraph :=
  .mk mulGraph_eval

instance mulValue_definable : 𝚺₁.DefinableFunction
    (fun v : Fin 10 → V => mulValue (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)) :=
  mulValue_defined.to_definable

theorem mulValue_zero (r0 z1 refl as m0 m1 ms Γ n : V) :
    mulValue r0 z1 refl as m0 m1 ms Γ n 0 =
      specializeCtxValue Γ (m0BodyCode : V) (Arithmetic.numeral n) m0 := by
  simp [mulValue, MulRec.construction]

theorem mulValue_one (r0 z1 refl as m0 m1 ms Γ n : V) :
    mulValue r0 z1 refl as m0 m1 ms Γ n 1 =
      specializeCtxValue Γ (m1BodyCode : V) (Arithmetic.numeral n) m1 := by
  simpa [mulValue, MulRec.construction] using
    (PR.Construction.result_succ (MulRec.construction (V := V))
      ![r0, z1, refl, as, m0, m1, ms, Γ, n] 0)

theorem mulValue_succ (r0 z1 refl as m0 m1 ms Γ n k : V) (hk : 0 < k) :
    mulValue r0 z1 refl as m0 m1 ms Γ n (k + 1) =
      mulPositiveValue r0 z1 refl as ms Γ n k (mulValue r0 z1 refl as m0 m1 ms Γ n k) := by
  simp [mulValue, MulRec.construction, ne_of_gt hk]

theorem mulGraph_total (r0 z1 refl as m0 m1 ms Γ n m : V) :
    ∃ o : V, mulGraph.val.Evalb ![o, r0, z1, refl, as, m0, m1, ms, Γ, n, m] :=
  ⟨mulValue r0 z1 refl as m0 m1 ms Γ n m, (mulGraph_iff _ _ _ _ _ _ _ _ _ _ _).mpr rfl⟩

theorem mulGraph_functional {o o' r0 z1 refl as m0 m1 ms Γ n m : V}
    (h : mulGraph.val.Evalb ![o, r0, z1, refl, as, m0, m1, ms, Γ, n, m])
    (h' : mulGraph.val.Evalb ![o', r0, z1, refl, as, m0, m1, ms, Γ, n, m]) : o = o' :=
  ((mulGraph_iff _ _ _ _ _ _ _ _ _ _ _).mp h).trans
    ((mulGraph_iff _ _ _ _ _ _ _ _ _ _ _).mp h').symm

end Internal

theorem mulPositiveValue_nat (r0 z1 refl as ms Γ n k ih : ℕ) :
    mulPositiveValue r0 z1 refl as ms Γ n k ih = mulPositiveCode r0 z1 refl as ms Γ n k ih := by
  simp only [mulPositiveValue, mulPositiveCode, natCast_nat, instance4Value_nat,
    specialize4Value_nat, applyCtxValue_nat, consequentValue_nat, addValue_nat]

theorem mulValue_nat (r0 z1 refl as m0 m1 ms Γ n m : ℕ) :
    mulValue r0 z1 refl as m0 m1 ms Γ n m = mulCtx r0 z1 refl as m0 m1 ms Γ n m := by
  induction m with
  | zero => simp [mulValue_zero, mulCtx_zero, numeralTermCodeValue_nat, specializeCtxValue_nat]
  | succ k ih =>
    by_cases hk : k = 0
    · subst k
      simp [mulValue_one, mulCtx_one, numeralTermCodeValue_nat, specializeCtxValue_nat]
    · rw [mulValue_succ _ _ _ _ _ _ _ _ _ _ (Nat.pos_of_ne_zero hk),
        mulCtx_succ _ _ _ _ _ _ _ _ _ _ (Nat.pos_of_ne_zero hk), ih, mulPositiveValue_nat]

theorem mulGraph_nat_iff (o r0 z1 refl as m0 m1 ms Γ n m : ℕ) :
    mulGraph.val.Evalb ![o, r0, z1, refl, as, m0, m1, ms, Γ, n, m] ↔
      o = mulCtx r0 z1 refl as m0 m1 ms Γ n m := by
  rw [mulGraph_iff, mulValue_nat]

end FailureOfComposition.NativeNumeralArithmetic
