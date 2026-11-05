/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46UniformTraceCoding

/-! # A literal arithmetic program for bounded earlier-stage failure

The program folds the actual total stage interpreter. Its all-model meaning
is proved by PA-internal induction independently of any native certificate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator

namespace CategoricalEssentialIncompleteness.V46.UniformTrace

def earlierStep : Code 4 :=
  codeIfPos (codeHistoryEvaluator.comp ![Code.proj 0, Code.proj 2, Code.proj 3])
    (Code.zero 4) (Code.proj 1)

/-- Arguments are bound, program index, and input. The bound itself is
not checked: the primitive recursion consumes exactly its earlier indices. -/
def earlierCode : Code 3 := codePrec (Code.one 2) earlierStep

def earlierGraph : 𝚺₁.Semisentence 4 := .mkSigma (code earlierCode) (code_sigma_one earlierCode)

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance flagsLocalInstance1 : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance flagsLocalInstance2 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance flagsLocalInstance3 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance
local instance flagsLocalInstance4 : DecidableEq M := Classical.decEq M

instance stageValue_defined :
    𝚺₁-Function₃ (stageValue : M → M → M → M) via evalnGraphFormula := .mk fun v => by
  have hv : ![v 0, v 1, v 2, v 3] = v := (Matrix.fun_eq_vec_four v).symm
  have h2 : Fin.succ (2 : Fin 3) = (3 : Fin 4) := by decide
  simpa only [hv, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, h2] using
    stageFormula_eval (v 0) (v 1) (v 2) (v 3)
instance stageValue_definable : 𝚺₁-Function₃ (stageValue : M → M → M → M) :=
  stageValue_defined.to_definable
instance stageValue_definable' (Γ m) : Γ-[m + 1]-Function₃ (stageValue : M → M → M → M) :=
  stageValue_definable.of_sigmaOne

theorem stage_inputs_value {n : ℕ} (S E X : Code n) (s e x : M) (v : Fin n → M)
    (hS : Semiformula.Evalb (s :> v) (code S))
    (hE : Semiformula.Evalb (e :> v) (code E))
    (hX : Semiformula.Evalb (x :> v) (code X)) :
    Semiformula.Evalb (stageValue s e x :> v) (code (codeHistoryEvaluator.comp ![S, E, X])) := by
  apply (eval_comp_iff codeHistoryEvaluator ![S, E, X] (stageValue s e x) v).mpr
  refine ⟨![s, e, x], stageValue_spec s e x, ?_⟩
  intro i
  fin_cases i
  · exact hS
  · exact hE
  · exact hX

/-- The branch decision concerns a numerical value already supplied by
the actual stage graph. It never negates an arbitrary Sigma-one relation. -/
theorem if_zero_value {n : ℕ} (C A B : Code n) (c a b : M) (v : Fin n → M)
    (hC : Semiformula.Evalb (c :> v) (code C))
    (hA : Semiformula.Evalb (a :> v) (code A))
    (hB : Semiformula.Evalb (b :> v) (code B)) :
    Semiformula.Evalb ((if c = 0 then b else a) :> v) (code (codeIfPos C A B)) := by
  by_cases hc : c = 0
  · simp only [ite_eq_left hc]
    exact eval_codeIfPos_of C A B c a b b v hC hA hB (Or.inr ⟨hc, rfl⟩)
  · simp only [ite_eq_right hc]
    exact eval_codeIfPos_of C A B c a b a v hC hA hB
      (Or.inl ⟨lt_of_le_of_ne (FFL.FirstOrder.Arithmetic.zero_le c) (Ne.symm hc), rfl⟩)

theorem earlierStep_value (i previous e x : M) :
    Semiformula.Evalb ((if stageValue i e x = 0 then previous else 0) :> ![i, previous, e, x])
      (code earlierStep) := by
  apply if_zero_value
    (codeHistoryEvaluator.comp ![Code.proj (0 : Fin 4), Code.proj 2, Code.proj 3])
    (Code.zero 4) (Code.proj 1) (stageValue i e x) 0 previous ![i, previous, e, x]
  · exact stage_inputs_value (Code.proj (0 : Fin 4)) (Code.proj 2) (Code.proj 3)
      i e x ![i, previous, e, x]
      ((eval_proj_iff _ _ _).mpr rfl) ((eval_proj_iff _ _ _).mpr rfl)
      ((eval_proj_iff _ _ _).mpr rfl)
  · exact (eval_zero_iff _ _).mpr rfl
  · exact (eval_proj_iff _ _ _).mpr rfl

theorem earlier_exists (s e x : M) :
    ∃ flag : M, Semiformula.Evalb ![flag, s, e, x] (code earlierCode) :=
  eval_codePrec_exists_of_total (Code.one 2) earlierStep s ![e, x]
    ⟨1, (eval_one_iff _ _).mpr rfl⟩
    (fun i _ previous => ⟨_, earlierStep_value i previous e x⟩)

noncomputable def earlier (s e x : M) : M := Classical.choose (earlier_exists s e x)

theorem earlier_spec (s e x : M) :
    Semiformula.Evalb ![earlier s e x, s, e, x] (code earlierCode) :=
  Classical.choose_spec (earlier_exists s e x)

@[simp] theorem earlierGraph_eval (o s e x : M) :
    earlierGraph.val.Evalb ![o, s, e, x] ↔ o = earlier s e x := by
  change Semiformula.Evalb ![o, s, e, x] (code earlierCode) ↔ o = earlier s e x
  constructor
  · exact fun h => eval_unique h (earlier_spec s e x)
  · rintro rfl
    exact earlier_spec s e x

instance earlier_defined :
    𝚺₁-Function₃ (earlier : M → M → M → M) via earlierGraph := .mk fun v => by
  have hv : ![v 0, v 1, v 2, v 3] = v := (Matrix.fun_eq_vec_four v).symm
  have h2 : Fin.succ (2 : Fin 3) = (3 : Fin 4) := by decide
  simpa only [hv, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, h2] using
    earlierGraph_eval (v 0) (v 1) (v 2) (v 3)
instance earlier_definable : 𝚺₁-Function₃ (earlier : M → M → M → M) := earlier_defined.to_definable
instance earlier_definable' (Γ m) : Γ-[m + 1]-Function₃ (earlier : M → M → M → M) :=
  earlier_definable.of_sigmaOne

@[simp] theorem earlier_zero (e x : M) : earlier 0 e x = 1 := by
  exact (eval_one_iff _ _).mp
    (eval_codePrec_zero (Code.one 2) earlierStep (earlier 0 e x) ![e, x] (earlier_spec 0 e x))

@[simp] theorem earlier_succ (s e x : M) :
    earlier (s + 1) e x = if stageValue s e x = 0 then earlier s e x else 0 := by
  obtain ⟨previous, hprevious, hstep⟩ :=
    eval_codePrec_succ (Code.one 2) earlierStep s (earlier (s + 1) e x) ![e, x]
      (earlier_spec (s + 1) e x)
  have hp : previous = earlier s e x := eval_unique hprevious (earlier_spec s e x)
  subst previous
  exact eval_unique hstep (earlierStep_value s (earlier s e x) e x)

/-- An opaque numerical fold lemma keeps definability synthesis independent
of the size of the concrete arithmetic program supplied at its application. -/
private theorem zero_fold_one_iff (F B : M → M → M → M)
    [𝚺₁-Function₃ F] [𝚺₁-Function₃ B]
    (hzero : ∀ e x : M, F 0 e x = 1)
    (hstep : ∀ s e x : M, F (s+1) e x = if B s e x = 0 then F s e x else 0)
    (s e x : M) : F s e x = 1 ↔ ∀ r < s, B r e x = 0 := by
  let foldPiF : 𝚷₁-Function₃ F :=
    HierarchySymbol.DefinableFunction.of_sigmaOne (inferInstance : 𝚺₁-Function₃ F)
  let foldPiB : 𝚷₁-Function₃ B :=
    HierarchySymbol.DefinableFunction.of_sigmaOne (inferInstance : 𝚺₁-Function₃ B)
  induction s using ISigma1.pi1_succ_induction
  · definability
  case zero => simp [hzero]
  case succ s ih =>
    rw [hstep]
    by_cases hs : B s e x = 0
    · simp only [ite_eq_left hs, ih]
      constructor
      · intro h r hr
        rcases (lt_or_eq_of_le (Arithmetic.lt_succ_iff_le.mp hr)) with hlt | rfl
        · exact h r hlt
        · exact hs
      · intro h r hr
        exact h r (lt_trans hr (by simp))
    · simp only [ite_eq_right hs, zero_ne_one, false_iff]
      intro h
      exact hs (h s (by simp))

theorem earlier_one_iff (s e x : M) :
    earlier s e x = 1 ↔ ∀ r < s, stageValue r e x = 0 :=
  zero_fold_one_iff earlier stageValue earlier_zero earlier_succ s e x

end Models
end CategoricalEssentialIncompleteness.V46.UniformTrace
