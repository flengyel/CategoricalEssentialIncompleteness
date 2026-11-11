/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceFlags

/-! # The actual halving program computes division in every PA model

The input of the induction is an arbitrary model element. This supplies the
internal-index decoder step that is unavailable from numeral-only evaluation.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode

namespace CategoricalEssentialIncompleteness.V46.UniformTrace
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance halvingLocalInstance1 : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance halvingLocalInstance2 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance halvingLocalInstance3 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance
local instance halvingLocalInstance4 : DecidableEq M := Classical.decEq M

theorem half_succ (a : M) :
    (a + 1) / 2 = if a % 2 = 0 then a / 2 else a / 2 + 1 := by
  rcases mod_two a with ha | ha
  · have he : a = 2 * (a / 2) := by simpa only [ha, add_zero] using (div_add_mod a 2).symm
    have hd := div_mul_add' (a / 2) (2 : M) (r := 1) (by simp)
    simpa only [ite_eq_left ha, ← he] using hd
  · have he : a = 2 * (a / 2) + 1 := by simpa only [ha] using (div_add_mod a 2).symm
    have hn : a % 2 ≠ 0 := by rw [ha]; exact Arithmetic.one_ne_zero
    rw [ite_eq_right hn]
    calc
      (a + 1) / 2 = (2 * (a / 2 + 1)) / 2 := by
        apply congrArg (fun z : M => z / 2)
        calc
          a + 1 = (2 * (a / 2) + 1) + 1 := congrArg (fun z : M => z + 1) he
          _ = 2 * (a / 2 + 1) := by
            rw [mul_add, mul_one, add_assoc]
            norm_num
      _ = a / 2 + 1 := by
        simpa only [add_zero] using
          div_mul_add' (a / 2 + 1) (2 : M) (r := 0) (by simp)

theorem half_step_value (a previous : M) :
    Semiformula.Evalb
      ![if a % 2 = 0 then previous else previous + 1, a, previous]
      (code (codeIfPos (codeBodd (Code.proj (0 : Fin 2)))
        (codeSucc (Code.proj 1)) (Code.proj 1))) := by
  have ha : Semiformula.Evalb (a :> ![a, previous]) (code (Code.proj (0 : Fin 2))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have hp : Semiformula.Evalb (previous :> ![a, previous]) (code (Code.proj (1 : Fin 2))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have ht : Semiformula.Evalb ((2 : M) :> ![a, previous]) (code (codeConst (n := 2) 2)) :=
    (eval_codeConst_iff _ _ _).mpr (by simp)
  exact if_zero_value _ _ _ (a % 2) (previous + 1) previous ![a, previous]
    (eval_codeRem _ _ a 2 ![a, previous] ha ht)
    ((eval_codeSucc_iff _ _ _).mpr ⟨previous, hp, rfl⟩) hp

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
private theorem half_relation_definable :
    𝚺₁.Definable (fun v : Fin 2 → M => Semiformula.Evalb ![v 0, v 1] (code codeDiv2Unary)) := by
  let R : 𝚺₁.Semisentence 2 := .mkSigma (code codeDiv2Unary) (code_sigma_one codeDiv2Unary)
  have h : 𝚺₁.Definable (fun v : Fin 2 → M => R.val.Evalb v) :=
    HierarchySymbol.Defined.to_definable R (.mk (fun _ => Iff.rfl))
  exact h.of_iff fun v => by
    rw [(Matrix.fun_eq_vec_two v).symm]
    rfl

theorem half_unary_value_eq (a o : M)
    (h : Semiformula.Evalb ![o, a] (code codeDiv2Unary)) : o = a / 2 := by
  have hall : ∀ a : M, ∀ o : M,
      Semiformula.Evalb ![o, a] (code codeDiv2Unary) → o = a / 2 := by
    intro a
    induction a using ISigma1.pi1_succ_induction
    · apply HierarchySymbol.Definable.all
      exact HierarchySymbol.Definable.imp half_relation_definable (by definability)
    case zero =>
      intro o ho
      have hz := eval_codePrec_zero _ _ o ![] ho
      simpa only [Arithmetic.zero_div] using (eval_zero_iff o ![]).mp hz
    case succ a ih =>
      intro o ho
      obtain ⟨previous, hp, hs⟩ := eval_codePrec_succ _ _ a o ![] ho
      have hpv := ih previous hp
      have he := eval_unique hs (half_step_value a previous)
      rw [he, hpv, half_succ]
  exact hall a o h

theorem half_unary_value (a : M) :
    Semiformula.Evalb ![a / 2, a] (code codeDiv2Unary) := by
  obtain ⟨o, ho⟩ := eval_codePrec_exists_of_total (Code.zero 0)
    (codeIfPos (codeBodd (Code.proj (0 : Fin 2))) (codeSucc (Code.proj 1)) (Code.proj 1))
    a ![] ⟨0, (eval_zero_iff _ _).mpr rfl⟩
    (fun i _ previous => ⟨_, half_step_value i previous⟩)
  have he := half_unary_value_eq a o ho
  rwa [he] at ho

theorem half_value {n : ℕ} (A : Code n) (a : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (a :> v) (code A)) :
    Semiformula.Evalb ((a / 2) :> v) (code (codeDiv2 A)) := by
  rw [codeDiv2, eval_comp_iff]
  refine ⟨![a], half_unary_value a, ?_⟩
  intro i
  fin_cases i
  exact hA

theorem half_value_iff {n : ℕ} (A : Code n) (a o : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (a :> v) (code A)) :
    Semiformula.Evalb (o :> v) (code (codeDiv2 A)) ↔ o = a / 2 := by
  constructor
  · exact fun h => eval_unique h (half_value A a v hA)
  · rintro rfl
    exact half_value A a v hA

end Models
end CategoricalEssentialIncompleteness.V46.UniformTrace
