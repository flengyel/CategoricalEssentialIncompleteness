/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeNumeralComparisonConstructor
public import FailureOfComposition.NativeNumeralAdditionGraph

/-!
# Compositional graphs of comparison proof functions

Every public graph has coordinates
`(output,r0,z1,refl,as,ltBridge,nltBridge,neForward,neReverse,Gamma,n,m)`.
Existential intermediate codes follow the executable operations in order.
In particular, `subDef` computes the truncated differences; the graph never
selects an output by a proof-acceptance condition.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeNumeralComparison

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open FailureOfComposition.NativeNumeralArithmetic
open FailureOfComposition.NativeEqualityTransport

open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeFamilyExtraction

noncomputable def eqGraph : 𝚺₁.Semisentence 12 := .mkSigma
  “o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m. ∃ nn, !numeralTermCodeGraph nn
    n ∧ !specializeCtxGraph o Γ ↑reflBodyCode nn refl”

noncomputable def ltGraph : 𝚺₁.Semisentence 12 := .mkSigma
  “o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m. ∃ d, !subDef d m (n + 1) ∧
    ∃ c, !instance4Graph c ↑ltBridgeBodyCode n d (d + n) m ∧
    ∃ e, !specialize4Graph e ↑ltBridgeBodyCode Γ ltBridge n d (d + n) m ∧
    ∃ a, !addGraph a r0 z1 refl as Γ d n ∧
    ∃ b, !addGraph b r0 z1 refl as Γ (d + n) 1 ∧
    ∃ f, !applyCtxGraph f Γ c e a ∧
    ∃ c2, !consequentGraph c2 c ∧ !applyCtxGraph o Γ c2 f b”

noncomputable def nltGraph : 𝚺₁.Semisentence 12 := .mkSigma
  “o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m. ∃ d, !subDef d n m ∧
    ∃ c, !instance3Graph c ↑nltBridgeBodyCode m d n ∧
    ∃ e, !specialize3Graph e ↑nltBridgeBodyCode Γ nltBridge m d n ∧
    ∃ a, !addGraph a r0 z1 refl as Γ d m ∧ !applyCtxGraph o Γ c e a”

noncomputable def neGraph : 𝚺₁.Semisentence 12 := .mkSigma
  “o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m. (n < m ∧ ∃ c, !instance2Graph c
    ↑neForwardBodyCode n m ∧
      ∃ e, !specialize2Graph e ↑neForwardBodyCode Γ neForward n m ∧
      ∃ a, !ltGraph a r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m ∧
      !applyCtxGraph o Γ c e a) ∨
    (¬(n < m) ∧ ∃ c, !instance2Graph c ↑neReverseBodyCode n m ∧
      ∃ e, !specialize2Graph e ↑neReverseBodyCode Γ neReverse n m ∧
      ∃ a, !ltGraph a r0 z1 refl as ltBridge nltBridge neForward neReverse Γ m n ∧
      !applyCtxGraph o Γ c e a)”

noncomputable def signedEqGraph : 𝚺₁.Semisentence 12 := .mkSigma
  “o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m. (n = m ∧ !eqGraph o r0 z1 refl
    as ltBridge nltBridge neForward neReverse Γ n m) ∨
    (n ≠ m ∧ !neGraph o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m)”

noncomputable def signedLtGraph : 𝚺₁.Semisentence 12 := .mkSigma
  “o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m. (n < m ∧ !ltGraph o r0 z1 refl
    as ltBridge nltBridge neForward neReverse Γ n m) ∨
    (¬(n < m) ∧ !nltGraph o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m)”

section Internal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

noncomputable def eqValue (_r0 _z1 refl _as _ltBridge _nltBridge _neForward _neReverse Γ n _m :
  V) : V :=
  specializeCtxValue Γ (reflBodyCode : V) (Arithmetic.numeral n) refl

@[simp] theorem eqGraph_eval (v : Fin 12 → V) :
    eqGraph.val.Evalb v ↔ v 0 = eqValue (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v
      10) (v 11) := by
  simp [eqGraph, eqValue, numeralTermCodeGraph_iff, Tarski.Structure.numeral_eq_numeral,
    numeral_eq_natCast_app]

theorem eqGraph_iff (o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V) :
    eqGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ, n, m] ↔
      o = eqValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m := eqGraph_eval _

theorem eqGraph_total (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V) :
    ∃ o, eqGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ,
      n, m] := by
  exact ⟨eqValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m, (eqGraph_iff _ _ _
    _ _ _ _ _ _ _ _ _).mpr rfl⟩

theorem eqGraph_functional {o p r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V}
    (ho : eqGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ,
      n, m])
    (hp : eqGraph.val.Evalb ![p, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ,
      n, m]) : o = p := by
  exact ((eqGraph_eval _).mp ho).trans ((eqGraph_eval _).mp hp).symm

noncomputable def ltValue (r0 z1 refl as ltBridge _nltBridge _neForward _neReverse Γ n m : V) : V :=
  let d := m - (n + 1)
  let c := instance4Value (ltBridgeBodyCode : V) n d (d + n) m
  let e := specialize4Value (ltBridgeBodyCode : V) Γ ltBridge n d (d + n) m
  applyCtxValue Γ (consequentValue c)
    (applyCtxValue Γ c e (addValue r0 z1 refl as Γ d n))
    (addValue r0 z1 refl as Γ (d + n) 1)

@[simp] theorem ltGraph_eval (v : Fin 12 → V) :
    ltGraph.val.Evalb v ↔ v 0 = ltValue (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v
      10) (v 11) := by
  simp [ltGraph, ltValue, sub_defined.iff, consequentGraph_iff,
    Tarski.Structure.numeral_eq_numeral, numeral_eq_natCast_app]

theorem ltGraph_iff (o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V) :
    ltGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ, n, m] ↔
      o = ltValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m := ltGraph_eval _

theorem ltGraph_total (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V) :
    ∃ o, ltGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ,
      n, m] := by
  exact ⟨ltValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m, (ltGraph_iff _ _ _
    _ _ _ _ _ _ _ _ _).mpr rfl⟩

theorem ltGraph_functional {o p r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V}
    (ho : ltGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ,
      n, m])
    (hp : ltGraph.val.Evalb ![p, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ,
      n, m]) : o = p := by
  exact ((ltGraph_eval _).mp ho).trans ((ltGraph_eval _).mp hp).symm

noncomputable def nltValue (r0 z1 refl as _ltBridge nltBridge _neForward _neReverse Γ n m : V) :
  V :=
  let d := n - m
  let c := instance3Value (nltBridgeBodyCode : V) m d n
  applyCtxValue Γ c (specialize3Value (nltBridgeBodyCode : V) Γ nltBridge m d n)
    (addValue r0 z1 refl as Γ d m)

@[simp] theorem nltGraph_eval (v : Fin 12 → V) :
    nltGraph.val.Evalb v ↔ v 0 = nltValue (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
      (v 10) (v 11) := by
  simp [nltGraph, nltValue, sub_defined.iff, Tarski.Structure.numeral_eq_numeral,
    numeral_eq_natCast_app]

theorem nltGraph_iff (o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V) :
    nltGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ, n, m] ↔
      o = nltValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m := nltGraph_eval _

theorem nltGraph_total (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V) :
    ∃ o, nltGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ,
      n, m] := by
  exact ⟨nltValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m, (nltGraph_iff _ _
    _ _ _ _ _ _ _ _ _ _).mpr rfl⟩

theorem nltGraph_functional {o p r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V}
    (ho : nltGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse,
      Γ, n, m])
    (hp : nltGraph.val.Evalb ![p, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse,
      Γ, n, m]) : o = p := by
  exact ((nltGraph_eval _).mp ho).trans ((nltGraph_eval _).mp hp).symm

noncomputable def neValue (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V) : V :=
  if n < m then
    applyCtxValue Γ (instance2Value (neForwardBodyCode : V) n m)
      (specialize2Value (neForwardBodyCode : V) Γ neForward n m)
      (ltValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m)
  else
    applyCtxValue Γ (instance2Value (neReverseBodyCode : V) n m)
      (specialize2Value (neReverseBodyCode : V) Γ neReverse n m)
      (ltValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ m n)

@[simp] theorem neGraph_eval (v : Fin 12 → V) :
    neGraph.val.Evalb v ↔ v 0 = neValue (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9) (v
      10) (v 11) := by
  by_cases h : v 10 < v 11 <;>
    simp [neGraph, neValue, Tarski.Structure.numeral_eq_numeral, numeral_eq_natCast_app, h]

theorem neGraph_iff (o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V) :
    neGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ, n, m] ↔
      o = neValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m := neGraph_eval _

theorem neGraph_total (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V) :
    ∃ o, neGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ,
      n, m] := by
  exact ⟨neValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m, (neGraph_iff _ _ _
    _ _ _ _ _ _ _ _ _).mpr rfl⟩

theorem neGraph_functional {o p r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V}
    (ho : neGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ,
      n, m])
    (hp : neGraph.val.Evalb ![p, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ,
      n, m]) : o = p := by
  exact ((neGraph_eval _).mp ho).trans ((neGraph_eval _).mp hp).symm

noncomputable def signedEqValue (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V)
  : V :=
  if n = m then eqValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m
  else neValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m

@[simp] theorem signedEqGraph_eval (v : Fin 12 → V) :
    signedEqGraph.val.Evalb v ↔ v 0 = signedEqValue (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v
      8) (v 9) (v 10) (v 11) := by
  by_cases h : v 10 = v 11 <;>
    simp [signedEqGraph, signedEqValue, h]

theorem signedEqGraph_iff (o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V) :
    signedEqGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ,
      n, m] ↔
      o = signedEqValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m :=
        signedEqGraph_eval _

theorem signedEqGraph_total (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V) :
    ∃ o, signedEqGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward,
      neReverse, Γ, n, m] := by
  exact ⟨signedEqValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m,
    (signedEqGraph_iff _ _ _ _ _ _ _ _ _ _ _ _).mpr rfl⟩

theorem signedEqGraph_functional {o p r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m
  : V}
    (ho : signedEqGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward,
      neReverse, Γ, n, m])
    (hp : signedEqGraph.val.Evalb ![p, r0, z1, refl, as, ltBridge, nltBridge, neForward,
      neReverse, Γ, n, m]) : o = p := by
  exact ((signedEqGraph_eval _).mp ho).trans ((signedEqGraph_eval _).mp hp).symm

noncomputable def signedLtValue (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V)
  : V :=
  if n < m then ltValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m
  else nltValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m

@[simp] theorem signedLtGraph_eval (v : Fin 12 → V) :
    signedLtGraph.val.Evalb v ↔ v 0 = signedLtValue (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v
      8) (v 9) (v 10) (v 11) := by
  by_cases h : v 10 < v 11 <;>
    simp [signedLtGraph, signedLtValue, h]

theorem signedLtGraph_iff (o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V) :
    signedLtGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ,
      n, m] ↔
      o = signedLtValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m :=
        signedLtGraph_eval _

theorem signedLtGraph_total (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V) :
    ∃ o, signedLtGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward,
      neReverse, Γ, n, m] := by
  exact ⟨signedLtValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m,
    (signedLtGraph_iff _ _ _ _ _ _ _ _ _ _ _ _).mpr rfl⟩

theorem signedLtGraph_functional {o p r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m
  : V}
    (ho : signedLtGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward,
      neReverse, Γ, n, m])
    (hp : signedLtGraph.val.Evalb ![p, r0, z1, refl, as, ltBridge, nltBridge, neForward,
      neReverse, Γ, n, m]) : o = p := by
  exact ((signedLtGraph_eval _).mp ho).trans ((signedLtGraph_eval _).mp hp).symm

variable (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : V)

theorem signedEqValue_of_eq (h : n = m) :
    signedEqValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m = eqValue r0 z1
      refl as ltBridge nltBridge neForward neReverse Γ n m := by
  simp only [signedEqValue, ite_eq_left h]

theorem signedEqValue_of_ne (h : n ≠ m) :
    signedEqValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m = neValue r0 z1
      refl as ltBridge nltBridge neForward neReverse Γ n m := by
  simp only [signedEqValue, ite_eq_right h]

theorem signedLtValue_of_lt (h : n < m) :
    signedLtValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m = ltValue r0 z1
      refl as ltBridge nltBridge neForward neReverse Γ n m := by
  simp only [signedLtValue, ite_eq_left h]

theorem signedLtValue_of_nlt (h : ¬n < m) :
    signedLtValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m = nltValue r0 z1
      refl as ltBridge nltBridge neForward neReverse Γ n m := by
  simp only [signedLtValue, ite_eq_right h]

end Internal

theorem sub_nat (n m : ℕ) : Arithmetic.sub n m = Nat.sub n m := by
  symm
  apply sub_eq_iff.mpr
  constructor
  · intro h
    have h' : Nat.le m n := by
      rcases le_def.mp h with h | h
      · exact Nat.le_of_eq h
      · exact Nat.le_of_lt h
    exact (Nat.add_sub_of_le h').symm
  · intro h
    exact Nat.sub_eq_zero_of_le (Nat.le_of_lt h)

theorem modelSub_nat (n m : ℕ) :
    @HSub.hSub ℕ ℕ ℕ
      (@instHSub ℕ (FFL.FirstOrder.Arithmetic.instSub_foundation (V := ℕ))) n m = Nat.sub n m :=
  sub_nat n m

theorem eqValue_nat (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : ℕ) :
    eqValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m = eqCode r0 z1 refl as
      ltBridge nltBridge neForward neReverse Γ n m := by
  simp only [natCast_nat, eqValue, eqCode, specializeCtxValue_nat, numeralTermCodeValue_nat]

theorem eqGraph_nat_iff (o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : ℕ) :
    eqGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ, n, m] ↔
      o = eqCode r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m := by
  rw [eqGraph_iff, eqValue_nat]

theorem ltValue_nat (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : ℕ) :
    ltValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m = ltCode r0 z1 refl as
      ltBridge nltBridge neForward neReverse Γ n m := by
  simp only [natCast_nat, ltValue, ltCode, specialize4Value_nat, instance4Value_nat,
    consequentValue_nat,
    applyCtxValue_nat, addValue_nat, modelSub_nat]
  rfl

theorem ltGraph_nat_iff (o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : ℕ) :
    ltGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ, n, m] ↔
      o = ltCode r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m := by
  rw [ltGraph_iff, ltValue_nat]

theorem nltValue_nat (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : ℕ) :
    nltValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m = nltCode r0 z1 refl as
      ltBridge nltBridge neForward neReverse Γ n m := by
  simp only [natCast_nat, nltValue, nltCode, instance3Value_nat, specialize3Value_nat,
    applyCtxValue_nat,
    addValue_nat, modelSub_nat]
  rfl

theorem nltGraph_nat_iff (o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : ℕ) :
    nltGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ, n, m] ↔
      o = nltCode r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m := by
  rw [nltGraph_iff, nltValue_nat]

theorem neValue_nat (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : ℕ) :
    neValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m = neCode r0 z1 refl as
      ltBridge nltBridge neForward neReverse Γ n m := by
  simp only [natCast_nat, neValue, neCode, instance2Value_nat, specialize2Value_nat,
    applyCtxValue_nat,
    ltValue_nat]

theorem neGraph_nat_iff (o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : ℕ) :
    neGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ, n, m] ↔
      o = neCode r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m := by
  rw [neGraph_iff, neValue_nat]

theorem signedEqValue_nat (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : ℕ) :
    signedEqValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m = signedEqCode r0
      z1 refl as ltBridge nltBridge neForward neReverse Γ n m := by
  simp only [signedEqValue, signedEqCode, eqValue_nat, neValue_nat]

theorem signedEqGraph_nat_iff (o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : ℕ) :
    signedEqGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ,
      n, m] ↔
      o = signedEqCode r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m := by
  rw [signedEqGraph_iff, signedEqValue_nat]

theorem signedLtValue_nat (r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : ℕ) :
    signedLtValue r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m = signedLtCode r0
      z1 refl as ltBridge nltBridge neForward neReverse Γ n m := by
  simp only [signedLtValue, signedLtCode, ltValue_nat, nltValue_nat]

theorem signedLtGraph_nat_iff (o r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m : ℕ) :
    signedLtGraph.val.Evalb ![o, r0, z1, refl, as, ltBridge, nltBridge, neForward, neReverse, Γ,
      n, m] ↔
      o = signedLtCode r0 z1 refl as ltBridge nltBridge neForward neReverse Γ n m := by
  rw [signedLtGraph_iff, signedLtValue_nat]

end FailureOfComposition.NativeNumeralComparison
