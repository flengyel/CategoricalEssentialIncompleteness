/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRefill

/-! # Decidable sort skeletons for parser and value stacks -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.CodedObjectMembership

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

def sortsBlueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “o. o = 0”
  adjoin := .mkSigma “o block tail ih. ∃ k, !pi₂Def.val k block ∧ !adjoinDef.val o k ih”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def sortsConstruction : VecRec.Construction M sortsBlueprint where
  nil _ := 0
  adjoin _ block _ ih := adjoin (π₂ block) ih
  nil_defined := .mk fun v => by simp [sortsBlueprint]
  adjoin_defined := .mk fun v => by simp [sortsBlueprint]

/-- This total numerical function forgets values and whole words,
retaining precisely the finite decidable sort sequence. -/
noncomputable def sorts (stack : M) : M := sortsConstruction.result ![] stack

@[simp] theorem sorts_nil : sorts (0 : M) = 0 := by simp [sorts, sortsConstruction]
@[simp] theorem sorts_adjoin (block stack : M) :
    sorts (adjoin block stack) = adjoin (π₂ block) (sorts stack) := by
  simp [sorts, sortsConstruction]
end Models

def sortsGraph : 𝚺₁.Semisentence 2 := sortsBlueprint.resultDef

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance sortsDecidableEq : DecidableEq M := Classical.decEq M

@[simp] theorem sortsGraph_eval (o stack : M) :
    sortsGraph.val.Evalb ![o, stack] ↔ o = sorts stack := by
  have hp : (fun i : Fin 0 => (![o, stack] : Fin 2 → M) i.succ.succ) = ![] := by
    funext i
    exact i.elim0
  have he := (sortsConstruction (M := M)).eval_resultDef ![o, stack]
  rw [hp] at he
  change sortsBlueprint.resultDef.val.Evalb ![o, stack] ↔ o = sortsConstruction.result ![] stack
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using he

instance sorts_defined : 𝚺₁-Function₁ (sorts : M → M) via sortsGraph := .mk fun v => by
  have hv : ![v 0, v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa only [hv, Fin.succ_zero_eq_one] using sortsGraph_eval (v 0) (v 1)
instance sorts_definable : 𝚺₁-Function₁ (sorts : M → M) := sorts_defined.to_definable
instance sorts_definable' (Γ m) : Γ-[m + 1]-Function₁ (sorts : M → M) :=
  sorts_definable.of_sigmaOne

@[simp] theorem len_sorts (stack : M) : len (sorts stack) = len stack := by
  induction stack using adjoin_ISigma1.pi1_succ_induction
  · definability
  case nil => simp
  case adjoin block stack ih => simp [ih]

@[simp] theorem sorts_eq_zero (stack : M) : sorts stack = 0 ↔ stack = 0 := by
  rcases nil_or_adjoin stack with rfl | ⟨block, tail, rfl⟩ <;> simp

/-- The failure bit and the untouched tail's sort skeleton; the raw
payload of a successful reconstruction is deliberately discarded. -/
noncomputable def remainderKey (result : M) : M :=
  if result = 0 then 0 else adjoin 0 (sorts (sndIdx result))

@[simp] theorem remainderKey_zero : remainderKey (0 : M) = 0 := by simp [remainderKey]
@[simp] theorem remainderKey_adjoin (u rest : M) :
    remainderKey (adjoin u rest) = adjoin 0 (sorts rest) := by simp [remainderKey]

/-- Equal sort skeletons give exactly the same atomic structural
success test and the same untouched tail skeleton. -/
theorem refillLeaf_sorts (formula : Bool) (s left right : M)
    (h : sorts left = sorts right) :
    remainderKey (refillLeaf formula s left) = remainderKey (refillLeaf formula s right) := by
  rcases nil_or_adjoin left with rfl | ⟨l, ls, rfl⟩
  · have hr : right = 0 := (sorts_eq_zero right).mp (by simpa using h.symm)
    simp [hr, refillLeaf]
  · rcases nil_or_adjoin right with rfl | ⟨r, rs, rfl⟩
    · simp at h
    · have hh : π₂ l = π₂ r ∧ sorts ls = sorts rs := by simpa using h
      obtain ⟨hk, ht⟩ := hh
      by_cases hs : s = 0 <;> by_cases hl : π₂ l = (if formula then 1 else 0) <;>
        simp_all [refillLeaf]

/-- The complete finite-polynomial structural test depends only on
root shape and stack sorts, never on labels, values or Sigma-one
membership decisions. -/
theorem refill_sorts (q : RawPolynomial) (s left right : M)
    (h : sorts left = sorts right) :
    remainderKey (refill q s left) = remainderKey (refill q s right) := by
  induction q generalizing s left right with
  | term => exact refillLeaf_sorts false s left right h
  | formula => exact refillLeaf_sorts true s left right h
  | coefficient C => simpa [refill] using congrArg (adjoin (0 : M)) h
  | unit => by_cases hs : s = 0 <;> simp [refill, hs, h]
  | product a b ia ib =>
      have hr := ib (π₂ s) left right h
      rcases nil_or_adjoin (refill b (π₂ s) left) with hlr | ⟨lv, ls, hlr⟩
      · rcases nil_or_adjoin (refill b (π₂ s) right) with hrr | ⟨rv, rs, hrr⟩
        · simp [refill, hlr, hrr]
        · simp [hlr, hrr] at hr
      · rcases nil_or_adjoin (refill b (π₂ s) right) with hrr | ⟨rv, rs, hrr⟩
        · simp [hlr, hrr] at hr
        · have hrs : sorts ls = sorts rs := by simpa [hlr, hrr] using hr
          have hh := ia (π₁ s) ls rs hrs
          rcases nil_or_adjoin (refill a (π₁ s) ls) with hll | ⟨lu, lt, hll⟩
          · rcases nil_or_adjoin (refill a (π₁ s) rs) with hrl | ⟨ru, rt, hrl⟩
            · simp [refill, hlr, hrr, hll, hrl]
            · simp [hll, hrl] at hh
          · rcases nil_or_adjoin (refill a (π₁ s) rs) with hrl | ⟨ru, rt, hrl⟩
            · simp [hll, hrl] at hh
            · simpa [refill, hlr, hrr, hll, hrl] using hh
  | sum a b ia ib =>
      by_cases hk₀ : π₂ s = 0
      · have hl := ia (π₁ s) left right h
        rcases nil_or_adjoin (refill a (π₁ s) left) with hll | ⟨lu, lt, hll⟩ <;>
          rcases nil_or_adjoin (refill a (π₁ s) right) with hrl | ⟨ru, rt, hrl⟩
        · simp [refill, hk₀, hll, hrl]
        · simp [hll, hrl] at hl
        · simp [hll, hrl] at hl
        · simpa [refill, hk₀, hll, hrl] using hl
      · by_cases hk₁ : π₂ s = 1
        · have hr := ib (π₁ s) left right h
          rcases nil_or_adjoin (refill b (π₁ s) left) with hll | ⟨lu, lt, hll⟩ <;>
            rcases nil_or_adjoin (refill b (π₁ s) right) with hrl | ⟨ru, rt, hrl⟩
          · simp [refill, hk₁, hll, hrl]
          · simp [hll, hrl] at hr
          · simp [hll, hrl] at hr
          · simpa [refill, hk₁, hll, hrl] using hr
        · simp [refill, hk₀, hk₁]

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
