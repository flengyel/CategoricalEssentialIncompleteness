/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46UniformTraceFlags

/-! # A literal total arithmetic program for the actual trace predicate

The program uses the bounded earlier-stage fold and equality of actual
numeric outputs. Its PA graph comparison is proved over all models before
any standard primitive-recursion certificate is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator

namespace CategoricalEssentialIncompleteness.V46.UniformTrace

def traceArguments : Fin 3 → Code 3 :=
  ![codeUnpair₁ (Code.proj 2), Code.proj 0, Code.proj 1]

/-- Input order is program index, ordinary input, and trace code.
The result is exactly zero or one, and one means this trace is valid. -/
def traceProgram : Code 3 := codeMul
  (codeEq (codeHistoryEvaluator.comp traceArguments) (codeSucc (codeUnpair₂ (Code.proj 2))))
  (codeEq (earlierCode.comp traceArguments) (Code.one 3))

def traceProgramGraph : 𝚺₁.Semisentence 4 :=
  .mkSigma (code traceProgram) (code_sigma_one traceProgram)

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance programLocalInstance1 : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance programLocalInstance2 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance programLocalInstance3 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance
local instance programLocalInstance4 : DecidableEq M := Classical.decEq M
local instance programLocalInstance5 (p : Prop) : Decidable p := Classical.propDecidable p

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem eq_value {n : ℕ} (A B : Code n) (a b : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (a :> v) (code A))
    (hB : Semiformula.Evalb (b :> v) (code B)) :
    Semiformula.Evalb ((if a = b then 1 else 0) :> v) (code (codeEq A B)) := by
  apply (eval_codeEq_iff _ _ _ _).mpr
  refine ⟨a, b, hA, hB, ?_⟩
  by_cases h : a = b
  · exact Or.inl ⟨h, ite_eq_left h⟩
  · exact Or.inr ⟨h, ite_eq_right h⟩

theorem earlier_inputs_value {n : ℕ} (S E X : Code n) (s e x : M) (v : Fin n → M)
    (hS : Semiformula.Evalb (s :> v) (code S))
    (hE : Semiformula.Evalb (e :> v) (code E))
    (hX : Semiformula.Evalb (x :> v) (code X)) :
    Semiformula.Evalb (earlier s e x :> v) (code (earlierCode.comp ![S, E, X])) := by
  apply (eval_comp_iff earlierCode ![S, E, X] (earlier s e x) v).mpr
  refine ⟨![s, e, x], earlier_spec s e x, ?_⟩
  intro i
  fin_cases i
  · exact hS
  · exact hE
  · exact hX

/-- The positive and negative values are proved from the actual finite
program; no decision procedure for an arbitrary Sigma-one graph is assumed. -/
theorem traceProgram_value (e x t : M) :
    Semiformula.Evalb ![if traceFormula.val.Evalb ![e, x, t] then (1 : M) else 0, e, x, t]
      (code traceProgram) := by
  classical
  have hE : Semiformula.Evalb (e :> ![e, x, t]) (code (Code.proj (0 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have hX : Semiformula.Evalb (x :> ![e, x, t]) (code (Code.proj (1 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have hT : Semiformula.Evalb (t :> ![e, x, t]) (code (Code.proj (2 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have hS := eval_codeUnpair₁ (Code.proj (2 : Fin 3)) t ![e, x, t] hT
  have hO := eval_codeUnpair₂ (Code.proj (2 : Fin 3)) t ![e, x, t] hT
  have hsucc := (eval_codeSucc_iff (codeUnpair₂ (Code.proj (2 : Fin 3)))
    (π₂ t + 1) ![e, x, t]).mpr ⟨π₂ t, hO, rfl⟩
  have hH := stage_inputs_value (codeUnpair₁ (Code.proj (2 : Fin 3)))
    (Code.proj 0) (Code.proj 1) (π₁ t) e x ![e, x, t] hS hE hX
  have hF := earlier_inputs_value (codeUnpair₁ (Code.proj (2 : Fin 3)))
    (Code.proj 0) (Code.proj 1) (π₁ t) e x ![e, x, t] hS hE hX
  have hfirst := eq_value (codeHistoryEvaluator.comp traceArguments)
    (codeSucc (codeUnpair₂ (Code.proj 2))) (stageValue (π₁ t) e x) (π₂ t + 1)
    ![e, x, t] hH hsucc
  have hflag := eq_value (earlierCode.comp traceArguments) (Code.one 3)
    (earlier (π₁ t) e x) 1 ![e, x, t] hF ((eval_one_iff _ _).mpr rfl)
  have hmul := (eval_codeMul_iff
    (codeEq (codeHistoryEvaluator.comp traceArguments) (codeSucc (codeUnpair₂ (Code.proj 2))))
    (codeEq (earlierCode.comp traceArguments) (Code.one 3))
    ((if stageValue (π₁ t) e x = π₂ t + 1 then 1 else 0) *
      (if earlier (π₁ t) e x = 1 then 1 else 0)) ![e, x, t]).mpr
    ⟨if stageValue (π₁ t) e x = π₂ t + 1 then 1 else 0,
      if earlier (π₁ t) e x = 1 then 1 else 0, hfirst, hflag, rfl⟩
  have htruth : traceFormula.val.Evalb ![e, x, t] ↔
      stageValue (π₁ t) e x = π₂ t + 1 ∧ earlier (π₁ t) e x = 1 := by
    rw [traceFormula_eval, earlier_one_iff]
    rfl
  by_cases hfirst' : stageValue (π₁ t) e x = π₂ t + 1 <;>
    by_cases hflag' : earlier (π₁ t) e x = 1 <;>
    simpa only [traceProgram, traceArguments, htruth, hfirst', hflag',
      and_true, and_false, true_and, false_and, ite_true, ite_false, one_mul, zero_mul] using hmul

@[simp] theorem traceProgram_eval_one (e x t : M) :
    traceProgramGraph.val.Evalb ![(1 : M), e, x, t] ↔ traceFormula.val.Evalb ![e, x, t] := by
  classical
  change Semiformula.Evalb ![(1 : M), e, x, t] (code traceProgram) ↔ _
  constructor
  · intro h
    have he := eval_unique h (traceProgram_value e x t)
    by_contra hn
    simp only [ite_eq_right hn] at he
    exact Arithmetic.one_ne_zero he
  · intro h
    simpa only [ite_eq_left h] using traceProgram_value e x t

theorem graph_iff_program_trace (e x y : M) : graph.val.Evalb ![e, x, y] ↔
    ∃ t : M, traceProgramGraph.val.Evalb ![(1 : M), e, x, t] ∧ out t = y := by
  simp only [traceProgram_eval_one, graph_iff_trace]

end Models

def traceProgramComparisonSentence : ArithmeticSentence :=
  let C := traceProgramGraph
  let R := traceFormula
  “∀ e x t, !C.val 1 e x t ↔ !R.val e x t”

theorem traceProgram_comparison_PA : 𝗣𝗔 ⊢ traceProgramComparisonSentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simp [models_iff, traceProgramComparisonSentence]

def traceProgramTotalitySentence : ArithmeticSentence :=
  let C := traceProgramGraph
  “∀ e x t, ∃ flag, !C.val flag e x t ∧ ∀ other, !C.val other e x t → other = flag”

theorem traceProgram_totality_PA : 𝗣𝗔 ⊢ traceProgramTotalitySentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hh : ∀ e x t : M, ∃ flag : M, traceProgramGraph.val.Evalb ![flag,e,x,t] ∧
      ∀ other : M, traceProgramGraph.val.Evalb ![other,e,x,t] → other = flag := by
    intro e x t
    classical
    refine ⟨if traceFormula.val.Evalb ![e,x,t] then (1 : M) else 0,
      traceProgram_value e x t, ?_⟩
    intro other hother
    change Semiformula.Evalb ![other,e,x,t] (code traceProgram) at hother
    exact eval_unique hother (traceProgram_value e x t)
  simpa [models_iff, traceProgramTotalitySentence] using hh

def primitiveTraceGraphSentence : ArithmeticSentence :=
  let G := graph
  let C := traceProgramGraph
  “∀ e x y, !G.val e x y ↔ ∃ t, !C.val 1 e x t ∧ !pi₂Def.val y t”

theorem primitive_trace_graph_PA : 𝗣𝗔 ⊢ primitiveTraceGraphSentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simpa [models_iff, primitiveTraceGraphSentence, out, eq_comm] using
    (graph_iff_program_trace (M := M))

end CategoricalEssentialIncompleteness.V46.UniformTrace
