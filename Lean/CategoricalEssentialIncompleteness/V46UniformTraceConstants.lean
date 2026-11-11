/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceComposition
public import CategoricalEssentialIncompleteness.V46UniformTraceStageSelection
public import FailureOfComposition.ConcreteWitnessGraphs

/-! # A genuine internal compiler for constant-output program indices

The parameter is encoded as program syntax by an arithmetic primitive
recursion. Correctness for every successful computation and existence at
sufficient fuel are separate internal inductions. No assertion of uniform
persistence at arbitrary unknown program indices is used.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator

namespace CategoricalEssentialIncompleteness.V46.UniformTrace
open ProgramIndices

def constantIndexBlueprint : PR.Blueprint 0 where
  zero := .mkSigma “o. o = 0”
  succ := .mkSigma “o previous i. ∃ p, !pairDef.val p 1 previous ∧ o = 4 + 4 * p + 2”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance constantsLocalInstance1 : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance constantsLocalInstance2 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance constantsLocalInstance3 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance

def constantIndexConstruction : PR.Construction M constantIndexBlueprint where
  zero _ := 0
  succ _ _ previous := compIndex 1 previous
  zero_defined := .mk fun v => by simp [constantIndexBlueprint]
  succ_defined := .mk fun v => by simp [constantIndexBlueprint, compIndex]

noncomputable def constantIndex (a : M) : M := constantIndexConstruction.result ![] a

@[simp] theorem constantIndex_zero : constantIndex (0 : M) = 0 := by
  simp [constantIndex, constantIndexConstruction]

@[simp] theorem constantIndex_succ (a : M) :
    constantIndex (a + 1) = compIndex 1 (constantIndex a) := by
  simp [constantIndex, constantIndexConstruction]

end Models

def constantIndexGraph : 𝚺₁.Semisentence 2 := constantIndexBlueprint.resultDef

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance constantsLocalInstance4 : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance constantsLocalInstance5 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance constantsLocalInstance6 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance

@[simp] theorem constantIndexGraph_eval (o a : M) :
    constantIndexGraph.val.Evalb ![o, a] ↔ o = constantIndex a := by
  have hp : (fun i : Fin 0 => (![o, a] : Fin 2 → M) i.succ.succ) = ![] := by
    funext i
    exact i.elim0
  have he := (constantIndexConstruction (M := M)).result_defined_iff ![o, a]
  rw [hp] at he
  change constantIndexBlueprint.resultDef.val.Evalb ![o, a] ↔
    o = constantIndexConstruction.result ![] a
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using he

instance constantIndex_defined :
    𝚺₁-Function₁ (constantIndex : M → M) via constantIndexGraph := .mk fun v => by
  have hv : ![v 0, v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa only [hv, Fin.succ_zero_eq_one] using
    constantIndexGraph_eval (v 0) (v 1)
instance constantIndex_definable : 𝚺₁-Function₁ (constantIndex : M → M) :=
  constantIndex_defined.to_definable
instance constantIndex_definable' (Γ m) : Γ-[m + 1]-Function₁ (constantIndex : M → M) :=
  constantIndex_definable.of_sigmaOne

private theorem base_stage_iff (q : ℕ) (hq : q < 4) (s input output : M) :
    evalnGraphFormula.val.Evalb ![output + 1, s, (q : M), input] ↔
      input < s ∧ output = FailureOfComposition.ConcreteWitnessGraphs.baseOutput q input := by
  have hraw := (evalnCertificateFormula_eval_history_iff s (q : M) input output).symm
  have hbase := FailureOfComposition.ConcreteWitnessGraphs.base_computation_iff
    (M := M) q hq s input output
  exact hraw.trans hbase

theorem zero_stage_iff (s input output : M) :
    evalnGraphFormula.val.Evalb ![output + 1, s, (0 : M), input] ↔
      input < s ∧ output = 0 := by
  have hbase := base_stage_iff 0 (by decide) s input output
  have hvector : (![output + 1, s, ((0 : ℕ) : M), input] : Fin 4 → M) =
      ![output + 1, s, (0 : M), input] := by simp only [Nat.cast_zero]
  have hnormalized := Eq.mp (congrArg (fun v : Fin 4 → M =>
    evalnGraphFormula.val.Evalb v ↔ input < s ∧
      output = FailureOfComposition.ConcreteWitnessGraphs.baseOutput 0 input) hvector) hbase
  have houtput : (output = FailureOfComposition.ConcreteWitnessGraphs.baseOutput 0 input) ↔
      output = 0 := Iff.rfl
  exact hnormalized.trans (and_congr Iff.rfl houtput)

theorem succ_stage_iff (s input output : M) :
    evalnGraphFormula.val.Evalb ![output + 1, s, (1 : M), input] ↔
      input < s ∧ output = input + 1 := by
  have hbase := base_stage_iff 1 (by decide) s input output
  have hvector : (![output + 1, s, ((1 : ℕ) : M), input] : Fin 4 → M) =
      ![output + 1, s, (1 : M), input] := by simp only [Nat.cast_one]
  have hnormalized := Eq.mp (congrArg (fun v : Fin 4 → M =>
    evalnGraphFormula.val.Evalb v ↔ input < s ∧
      output = FailureOfComposition.ConcreteWitnessGraphs.baseOutput 1 input) hvector) hbase
  have houtput : (output = FailureOfComposition.ConcreteWitnessGraphs.baseOutput 1 input) ↔
      output = input + 1 := Iff.rfl
  exact hnormalized.trans (and_congr Iff.rfl houtput)

/-- Every successful execution of the internal constant program has
the prescribed output, even at a fuel below the sufficient bound below. -/
theorem constantIndex_correct (a s input output : M)
    (h : evalnGraphFormula.val.Evalb ![output + 1, s, constantIndex a, input]) : output = a := by
  have hall : ∀ a : M, ∀ s input output : M,
      stageValue s (constantIndex a) input = output + 1 → output = a := by
    intro a
    induction a using ISigma1.pi1_succ_induction
    · definability
    case zero =>
      intro s input output h
      have hh := (stageFormula_eval (output + 1) s (constantIndex 0) input).mpr h.symm
      exact ((zero_stage_iff s input output).mp (by simpa only [constantIndex_zero] using hh)).2
    case succ a ih =>
      intro s input output hn
      have h := (stageFormula_eval (output + 1) s (constantIndex (a + 1)) input).mpr hn.symm
      rw [constantIndex_succ, composition_stage_iff] at h
      obtain ⟨middle, hm, hs⟩ := h
      have he : middle = a := ih s input middle
        ((stageFormula_eval (middle + 1) s (constantIndex a) input).mp hm).symm
      have ho := ((succ_stage_iff s middle output).mp hs).2
      simpa only [he] using ho
  exact hall a s input output ((stageFormula_eval (output + 1) s (constantIndex a) input).mp h).symm

/-- The actual constant program succeeds at every internal stage that
is strictly above both the prescribed value and the supplied input. -/
theorem constantIndex_sufficient_stage (a s input : M) (ha : a < s) (hx : input < s) :
    evalnGraphFormula.val.Evalb ![a + 1, s, constantIndex a, input] := by
  have hall : ∀ a : M, a < s →
      stageValue s (constantIndex a) input = a + 1 := by
    intro a
    induction a using ISigma1.pi1_succ_induction
    · definability
    case zero =>
      intro _
      have hz := (zero_stage_iff s input 0).mpr ⟨hx, rfl⟩
      simpa only [constantIndex_zero] using
        ((stageFormula_eval ((0 : M) + 1) s 0 input).mp hz).symm
    case succ a ih =>
      intro has
      have ha' : a < s := lt_trans (by simp) has
      have hi := (stageFormula_eval (a + 1) s (constantIndex a) input).mpr (ih ha').symm
      have hs := (succ_stage_iff s a (a + 1)).mpr ⟨ha', rfl⟩
      have hc := (composition_stage_iff s 1 (constantIndex a) input (a + 1)).mpr ⟨a, hi, hs⟩
      rw [← constantIndex_succ] at hc
      exact ((stageFormula_eval ((a + 1) + 1) s (constantIndex (a + 1)) input).mp hc).symm
  exact (stageFormula_eval (a + 1) s (constantIndex a) input).mpr (hall a ha).symm

theorem constantIndex_graph (a input output : M) :
    graph.val.Evalb ![constantIndex a, input, output] ↔ output = a := by
  constructor
  · intro h
    obtain ⟨t, ht, ho⟩ := (graph_iff_trace (constantIndex a) input output).mp h
    have he := ((traceFormula_eval (constantIndex a) input t).mp ht).1
    rw [ho] at he
    exact constantIndex_correct a (π₁ t) input output
      ((stageFormula_eval (output + 1) (π₁ t) (constantIndex a) input).mpr he.symm)
  · intro hout
    subst output
    let fuel := a + input + 1
    have ha : a < fuel := by simp [fuel, add_assoc]
    have hx : input < fuel := by
      have hle : input ≤ a + input := by
        simpa only [zero_add] using
          add_le_add_left (FFL.FirstOrder.Arithmetic.zero_le a) input
      exact lt_of_le_of_lt hle (by simp [fuel])
    exact graph_of_consistent_stage (constantIndex a) input a
      (fun s z h => constantIndex_correct a s input z h) fuel
      (constantIndex_sufficient_stage a fuel input ha hx)

end Models

def constantIndexTotalSentence : ArithmeticSentence :=
  let C := constantIndexGraph
  “∀ a, ∃ p, !C.val p a ∧ ∀ q, !C.val q a → q = p”

theorem constantIndex_totality_PA : 𝗣𝗔 ⊢ constantIndexTotalSentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simp [models_iff, constantIndexTotalSentence]

def constantIndexGraphSentence : ArithmeticSentence :=
  let C := constantIndexGraph
  let G := graph
  “∀ a p x y, !C.val p a → (!G.val p x y ↔ y = a)”

theorem constantIndex_graph_PA : 𝗣𝗔 ⊢ constantIndexGraphSentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have hmodel : ∀ a p x y : M, constantIndexGraph.val.Evalb ![p, a] →
      (graph.val.Evalb ![p, x, y] ↔ y = a) := by
    intro a p x y hp
    have he : p = constantIndex a := (constantIndexGraph_eval p a).mp hp
    subst p
    exact constantIndex_graph a x y
  simpa [models_iff, constantIndexGraphSentence] using hmodel

end CategoricalEssentialIncompleteness.V46.UniformTrace
