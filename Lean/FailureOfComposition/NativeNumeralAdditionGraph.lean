/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeNumeralConstructor

/-!
# Structural internal recurrence for addition proofs

The blueprint specifies the very same zero, one, and positive-successor
operations as the executable constructor. Its six parameters are
`(r0,z1,refl,as,Gamma,n)`; the recursion variable is `m`. The public graph
reorders the blueprint's output/recursion/parameter coordinates to
`(output,r0,z1,refl,as,Gamma,n,m)`. Exactness holds throughout a PA model,
without validity assumptions on supplied seed or context codes.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeNumeralArithmetic

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeEqualityTransport
open FailureOfComposition.NativeFamilyExtraction

noncomputable def addOneGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “o z1 refl Γ n. (n = 0 ∧ o = z1) ∨
    (n ≠ 0 ∧ ∃ nn, !numeralTermCodeGraph nn n ∧
      ∃ t, !qqAddGraph t nn ↑Arithmetic.one ∧ !specializeCtxGraph o Γ ↑reflBodyCode t refl)”

noncomputable def addPositiveGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “o as Γ n k ih. ∃ c, !instance3Graph c ↑asBodyCode n k (n + k) ∧
    ∃ d, !specialize3Graph d ↑asBodyCode Γ as n k (n + k) ∧ !applyCtxGraph o Γ c d ih”

namespace AddRec

noncomputable def blueprint : PR.Blueprint 6 where
  zero := .mkSigma “o r0 z1 refl as Γ n.
    ∃ nn, !numeralTermCodeGraph nn n ∧ !specializeCtxGraph o Γ ↑r0BodyCode nn r0”
  succ := .mkSigma “o ih k r0 z1 refl as Γ n.
    (k = 0 ∧ !addOneGraph o z1 refl Γ n) ∨
    (k ≠ 0 ∧ !addPositiveGraph o as Γ n k ih)”

end AddRec

section Internal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def addOneValue (z1 refl Γ n : V) : V :=
  if n = 0 then z1 else specializeCtxValue Γ (reflBodyCode : V)
    (qqAdd (Arithmetic.numeral n) (Arithmetic.one : V)) refl

noncomputable def addPositiveValue (as Γ n k ih : V) : V :=
  applyCtxValue Γ (instance3Value (asBodyCode : V) n k (n + k))
    (specialize3Value (asBodyCode : V) Γ as n k (n + k)) ih

@[simp] theorem addOneGraph_eval (v : Fin 5 → V) :
    addOneGraph.val.Evalb v ↔ v 0 = addOneValue (v 1) (v 2) (v 3) (v 4) := by
  by_cases hn : v 4 = 0 <;>
    simp [addOneGraph, addOneValue, hn, numeralTermCodeGraph_iff, qqAdd_defined.iff,
      Tarski.Structure.numeral_eq_numeral, numeral_eq_natCast_app]

@[simp] theorem addPositiveGraph_eval (v : Fin 6 → V) :
    addPositiveGraph.val.Evalb v ↔
      v 0 = addPositiveValue (v 1) (v 2) (v 3) (v 4) (v 5) := by
  simp [addPositiveGraph, addPositiveValue, Tarski.Structure.numeral_eq_numeral,
    numeral_eq_natCast_app]

namespace AddRec

noncomputable def construction : PR.Construction V blueprint where
  zero v := specializeCtxValue (v 4) (r0BodyCode : V) (Arithmetic.numeral (v 5)) (v 0)
  succ v k ih := if k = 0 then addOneValue (v 1) (v 2) (v 4) (v 5)
    else addPositiveValue (v 3) (v 4) (v 5) k ih
  zero_defined := .mk fun v => by
    simp [blueprint, numeralTermCodeGraph_iff, Tarski.Structure.numeral_eq_numeral,
      numeral_eq_natCast_app]
  succ_defined := .mk fun v => by
    by_cases hk : v 2 = 0 <;> simp [blueprint, hk]

end AddRec

noncomputable def addValue (r0 z1 refl as Γ n m : V) : V :=
  AddRec.construction.result ![r0, z1, refl, as, Γ, n] m

noncomputable def addGraph : 𝚺₁.Semisentence 8 :=
  AddRec.blueprint.resultDef.rew (Rew.subst ![#0, #7, #1, #2, #3, #4, #5, #6])

theorem addGraph_iff (o r0 z1 refl as Γ n m : V) :
    addGraph.val.Evalb ![o, r0, z1, refl, as, Γ, n, m] ↔ o = addValue r0 z1 refl as Γ n m := by
  simpa [addGraph, addValue, Matrix.comp_vecCons''] using
    (AddRec.construction (V := V)).result_defined_iff ![o, m, r0, z1, refl, as, Γ, n]

@[simp] theorem addGraph_eval (v : Fin 8 → V) :
    addGraph.val.Evalb v ↔ v 0 = addValue (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) := by
  have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7] := by ext i; fin_cases i <;> rfl
  rw [hv]
  exact addGraph_iff _ _ _ _ _ _ _ _

instance addValue_defined : 𝚺₁.DefinedFunction
    (fun v : Fin 7 → V => addValue (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) addGraph :=
  .mk addGraph_eval

instance addValue_definable : 𝚺₁.DefinableFunction
    (fun v : Fin 7 → V => addValue (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) :=
  addValue_defined.to_definable

theorem addValue_zero (r0 z1 refl as Γ n : V) :
    addValue r0 z1 refl as Γ n 0 =
      specializeCtxValue Γ (r0BodyCode : V) (Arithmetic.numeral n) r0 := by
  simp [addValue, AddRec.construction]

theorem addValue_one (r0 z1 refl as Γ n : V) :
    addValue r0 z1 refl as Γ n 1 = addOneValue z1 refl Γ n := by
  simpa [addValue, AddRec.construction] using
    (PR.Construction.result_succ (AddRec.construction (V := V)) ![r0, z1, refl, as, Γ, n] 0)

theorem addValue_succ (r0 z1 refl as Γ n k : V) (hk : 0 < k) :
    addValue r0 z1 refl as Γ n (k + 1) =
      addPositiveValue as Γ n k (addValue r0 z1 refl as Γ n k) := by
  simp [addValue, AddRec.construction, ne_of_gt hk]

theorem addGraph_total (r0 z1 refl as Γ n m : V) :
    ∃ o : V, addGraph.val.Evalb ![o, r0, z1, refl, as, Γ, n, m] :=
  ⟨addValue r0 z1 refl as Γ n m, (addGraph_iff _ _ _ _ _ _ _ _).mpr rfl⟩

theorem addGraph_functional {o o' r0 z1 refl as Γ n m : V}
    (h : addGraph.val.Evalb ![o, r0, z1, refl, as, Γ, n, m])
    (h' : addGraph.val.Evalb ![o', r0, z1, refl, as, Γ, n, m]) : o = o' :=
  ((addGraph_iff _ _ _ _ _ _ _ _).mp h).trans ((addGraph_iff _ _ _ _ _ _ _ _).mp h').symm

end Internal

theorem addOneValue_nat (z1 refl Γ n : ℕ) : addOneValue z1 refl Γ n = addOneCode z1 refl Γ n := by
  simp only [addOneValue, addOneCode, natCast_nat, numeralTermCodeValue_nat,
    addTermCode_nat, specializeCtxValue_nat]

theorem addPositiveValue_nat (as Γ n k ih : ℕ) :
    addPositiveValue as Γ n k ih = addPositiveCode as Γ n k ih := by
  simp only [addPositiveValue, addPositiveCode, natCast_nat,
    instance3Value_nat, specialize3Value_nat, applyCtxValue_nat]

theorem addValue_nat (r0 z1 refl as Γ n m : ℕ) :
    addValue r0 z1 refl as Γ n m = addCtx r0 z1 refl as Γ n m := by
  induction m with
  | zero => simp [addValue_zero, addCtx_zero, numeralTermCodeValue_nat, specializeCtxValue_nat]
  | succ k ih =>
    by_cases hk : k = 0
    · subst k
      simpa [addCtx_one] using
        (addValue_one (V := ℕ) r0 z1 refl as Γ n).trans (addOneValue_nat z1 refl Γ n)
    · rw [addValue_succ _ _ _ _ _ _ _ (Nat.pos_of_ne_zero hk),
        addCtx_succ _ _ _ _ _ _ _ (Nat.pos_of_ne_zero hk), ih, addPositiveValue_nat]

theorem addGraph_nat_iff (o r0 z1 refl as Γ n m : ℕ) :
    addGraph.val.Evalb ![o, r0, z1, refl, as, Γ, n, m] ↔ o = addCtx r0 z1 refl as Γ n m := by
  rw [addGraph_iff, addValue_nat]

end FailureOfComposition.NativeNumeralArithmetic
