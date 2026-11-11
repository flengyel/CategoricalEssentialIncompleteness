/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceModelSnoc

/-! # History-vector prefix stability with arbitrary internal program indices

This proof reads the actual production history as the canonical arithmetic
vector that it is. The lookup index is a model element throughout. It never
replaces an arbitrary internal program index by a standard numeral.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.ModelHistory
open ModelLists

def historyGraph : 𝚺₁.Semisentence 2 :=
  .mkSigma (code codeEvaluatorHistory) (code_sigma_one codeEvaluatorHistory)

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance modelHistoryLocalInstance1 : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance modelHistoryLocalInstance2 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance modelHistoryLocalInstance3 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance
local instance modelHistoryLocalInstance4 : DecidableEq M := Classical.decEq M
local instance modelHistoryLocalInstance5 : DecidableLT M := Classical.decRel _

noncomputable def history (n : M) : M := Classical.choose (eval_codeEvaluatorHistory_exists n)

theorem history_spec (n : M) :
    Semiformula.Evalb ![history n, n] (code codeEvaluatorHistory) :=
  Classical.choose_spec (eval_codeEvaluatorHistory_exists n)

@[simp] theorem historyGraph_eval (o n : M) :
    historyGraph.val.Evalb ![o, n] ↔ o = history n := by
  change Semiformula.Evalb ![o, n] (code codeEvaluatorHistory) ↔ _
  constructor
  · exact fun h => eval_unique h (history_spec n)
  · rintro rfl
    exact history_spec n

instance history_defined : 𝚺₁-Function₁ (history : M → M) via historyGraph := .mk fun v => by
  have hv : ![v 0, v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa only [hv, Fin.succ_zero_eq_one] using historyGraph_eval (v 0) (v 1)
instance history_definable : 𝚺₁-Function₁ (history : M → M) := history_defined.to_definable
instance history_definable' (Γ m) : Γ-[m + 1]-Function₁ (history : M → M) :=
  history_definable.of_sigmaOne

@[simp] theorem len_history (n : M) : len (history n) = n :=
  eval_codeEvaluatorHistory_length_unique n (history n) (len (history n)) (history_spec n)
    (length_value (Code.proj (0 : Fin 1)) (history n) ![history n]
      ((eval_proj_iff _ _ _).mpr rfl))

/-- The actual history step appends one actual row. No interpretation
of that row or computation-certificate persistence is needed here. -/
theorem history_step (n : M) : ∃ row : M,
    history (n + 1) = concat (history n) row := by
  obtain ⟨prev, hprev, hstep⟩ := eval_codePrec_succ (codeListNil (n := 0))
    (codeEvaluatorTableStep (Code.proj (1 : Fin 2))) n (history (n + 1)) ![]
      (history_spec (n + 1))
  have hp : prev = history n := eval_unique hprev (history_spec n)
  subst prev
  have hproj : Semiformula.Evalb (history n :> ![n, history n])
      (code (Code.proj (1 : Fin 2))) := (eval_proj_iff _ _ _).mpr rfl
  obtain ⟨row, hrow⟩ := eval_codeEvaluatorRow_exists_of_value _ (history n) ![n, history n] hproj
  exact ⟨row, snoc_value_eq (Code.proj (1 : Fin 2))
    (codeEvaluatorRow (Code.proj (1 : Fin 2))) (history n) row (history (n + 1))
    ![n, history n] hproj hrow hstep⟩

/-- A numerical stability proof with the sequence function opaque avoids
normalizing the concrete closed evaluator during definability synthesis. -/
private theorem snoc_nth_stable (H : M → M) [𝚺₁-Function₁ H]
    (hlen : ∀ n : M, len (H n) = n)
    (hstep : ∀ n : M, ∃ row : M, H (n + 1) = concat (H n) row)
    (n m i : M) (hnm : n ≤ m) (hi : i < n) : nth (H m) i = nth (H n) i := by
  let sequencePi : 𝚷₁-Function₁ H :=
    HierarchySymbol.DefinableFunction.of_sigmaOne (inferInstance : 𝚺₁-Function₁ H)
  have hh : ∀ m : M, n ≤ m → nth (H m) i = nth (H n) i := by
    intro m
    induction m using ISigma1.pi1_succ_induction
    · definability
    case zero =>
      intro hn
      have hn0 : n = 0 := le_antisymm hn (FFL.FirstOrder.Arithmetic.zero_le n)
      exact False.elim (by simp [hn0] at hi)
    case succ m ih =>
      intro hnm
      by_cases he : n = m + 1
      · simp only [he]
      · have hnm' : n ≤ m := Arithmetic.lt_succ_iff_le.mp (lt_of_le_of_ne hnm he)
        obtain ⟨row, hr⟩ := hstep m
        rw [hr, concat_nth_lt _ _ (by simpa only [hlen] using lt_of_lt_of_le hi hnm')]
        exact ih hnm'
  exact hh m hnm

/-- An arbitrary old row keeps its value at every later internal history
length. Both indices remain arbitrary elements of the PA model. -/
theorem history_nth_stable (n m i : M) (hnm : n ≤ m) (hi : i < n) :
    nth (history m) i = nth (history n) i :=
  snoc_nth_stable history len_history history_step n m i hnm hi

noncomputable def lookup (table k q input : M) : M :=
  if ⟪k, q⟫ < len table then
    if input < len (nth table ⟪k, q⟫) then nth (nth table ⟪k, q⟫) input else 0
  else 0

theorem lookup_value {n : ℕ} (A K Q X : Code n) (table k q input : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (table :> v) (code A))
    (hK : Semiformula.Evalb (k :> v) (code K))
    (hQ : Semiformula.Evalb (q :> v) (code Q))
    (hX : Semiformula.Evalb (input :> v) (code X)) :
    Semiformula.Evalb (lookup table k q input :> v) (code (codeTableLookup A K Q X)) := by
  have hp := eval_codePair K Q k q v hK hQ
  have hrow := get_value A (codePair K Q) table ⟪k, q⟫ v hA hp
  have hone : Semiformula.Evalb ((1 : M) :> v) (code (codeConst (n := n) 1)) :=
    (eval_codeConst_iff _ _ _).mpr (by simp)
  rw [codeTableLookup_eq]
  by_cases hkey : ⟪k, q⟫ < len table
  · simp only [ite_eq_left hkey] at hrow
    have hsub := eval_codeSub _ _ (nth table ⟪k, q⟫ + 1) 1 v hrow hone
    rw [add_sub_self] at hsub
    have hentry := get_value _ X (nth table ⟪k, q⟫) input v hsub hX
    have hresult := eval_codeSub _ _
      (if input < len (nth table ⟪k, q⟫) then nth (nth table ⟪k, q⟫) input + 1 else 0)
      1 v hentry hone
    by_cases hin : input < len (nth table ⟪k, q⟫)
    · simpa only [lookup, ite_eq_left hkey, ite_eq_left hin, add_sub_self] using hresult
    · simpa only [lookup, ite_eq_left hkey, ite_eq_right hin, Arithmetic.zero_sub] using hresult
  · simp only [ite_eq_right hkey] at hrow
    have hsub := eval_codeSub _ _ 0 1 v hrow hone
    simp only [Arithmetic.zero_sub] at hsub
    have hentry := get_value _ X 0 input v hsub hX
    simp only [len_nil, not_lt_zero] at hentry
    have hresult := eval_codeSub _ _ 0 1 v hentry hone
    simpa only [lookup, ite_eq_right hkey, Arithmetic.zero_sub] using hresult

theorem lookup_value_iff {n : ℕ} (A K Q X : Code n) (table k q input o : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (table :> v) (code A))
    (hK : Semiformula.Evalb (k :> v) (code K))
    (hQ : Semiformula.Evalb (q :> v) (code Q))
    (hX : Semiformula.Evalb (input :> v) (code X)) :
    Semiformula.Evalb (o :> v) (code (codeTableLookup A K Q X)) ↔
      o = lookup table k q input := by
  constructor
  · exact fun h => eval_unique h (lookup_value A K Q X table k q input v hA hK hQ hX)
  · rintro rfl
    exact lookup_value A K Q X table k q input v hA hK hQ hX

theorem stageValue_eq_lookup (k q input : M) :
    stageValue k q input = lookup (history (⟪k, q⟫ + 1)) k q input := by
  have hkey := eval_codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3))
    k q ![k, q, input] ((eval_proj_iff _ _ _).mpr rfl) ((eval_proj_iff _ _ _).mpr rfl)
  have hsucc := (eval_codeSucc_iff _ _ _).mpr ⟨⟪k, q⟫, hkey, rfl⟩
  have hhistory : Semiformula.Evalb (history (⟪k, q⟫ + 1) :> ![k, q, input])
      (code (codeEvaluatorHistory.comp ![codeSucc
        (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)))])) := by
    apply (eval_comp_iff codeEvaluatorHistory
      ![codeSucc (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)))]
      (history (⟪k, q⟫ + 1)) ![k, q, input]).mpr
    refine ⟨![⟪k, q⟫ + 1], history_spec (⟪k, q⟫ + 1), ?_⟩
    intro i
    fin_cases i
    exact hsucc
  exact eval_unique (stageValue_spec k q input)
    (lookup_value (codeEvaluatorHistory.comp ![codeSucc
      (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)))])
      (Code.proj 0) (Code.proj 1) (Code.proj 2)
      (history (⟪k, q⟫ + 1)) k q input ![k, q, input] hhistory
      ((eval_proj_iff _ _ _).mpr rfl) ((eval_proj_iff _ _ _).mpr rfl)
      ((eval_proj_iff _ _ _).mpr rfl))

/-- The missing earlier-row bridge is uniform in `q : M`. It reads an
actual history at an arbitrary later internal length. -/
theorem lookup_history_eq (N k q input : M) (hrow : ⟪k, q⟫ < N) :
    lookup (history N) k q input = stageValue k q input := by
  rw [stageValue_eq_lookup]
  have he := history_nth_stable (⟪k, q⟫ + 1) N ⟪k, q⟫
    (Arithmetic.succ_le_iff_lt.mpr hrow) (by simp)
  simp only [lookup, len_history, ite_eq_left hrow, lt_add_one, ite_eq_left, he]

theorem prefix_lookup_iff {n : ℕ} (A K Q X : Code n) (N H k q input o : M)
    (v : Fin n → M) (hH : Semiformula.Evalb ![H, N] (code codeEvaluatorHistory))
    (hrow : ⟪k, q⟫ < N)
    (hA : Semiformula.Evalb (H :> v) (code A))
    (hK : Semiformula.Evalb (k :> v) (code K))
    (hQ : Semiformula.Evalb (q :> v) (code Q))
    (hX : Semiformula.Evalb (input :> v) (code X)) :
    Semiformula.Evalb (o :> v) (code (codeTableLookup A K Q X)) ↔
      evalnGraphFormula.val.Evalb ![o, k, q, input] := by
  have he : H = history N := eval_unique hH (history_spec N)
  subst H
  rw [lookup_value_iff A K Q X _ k q input o v hA hK hQ hX,
    lookup_history_eq N k q input hrow, stageFormula_eval]

end Models
end CategoricalEssentialIncompleteness.V46.UniformTrace.ModelHistory
