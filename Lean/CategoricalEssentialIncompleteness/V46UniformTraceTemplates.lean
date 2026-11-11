/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceConstants
public import CategoricalEssentialIncompleteness.V46UniformTracePairing

/-! # A genuine parameter compiler for each fixed standard program

The parameter is arbitrary data in the PA model. Only the template index is
external and fixed, which is exactly where the existing persistence theorem
is used. The new dynamic constant/pair/composition indices are handled by
their actual internal stage equations and independently proved soundness.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator
open FailureOfComposition FailureOfComposition.ConcreteEvaluator

namespace CategoricalEssentialIncompleteness.V46.UniformTrace
open ProgramIndices

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance templatesLocalInstance1 : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance templatesLocalInstance2 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance templatesLocalInstance3 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance

theorem standard_graph_stages_iff (v : ℕ) (input output : M) :
    graph.val.Evalb ![(v : M), input, output] ↔
      ∃ s : M, evalnGraphFormula.val.Evalb ![output + 1, s, (v : M), input] := by
  have h := canonicalPartrecGraphFormula_eval_iff_eventualGraph (M := M) v input output
  simp only [numeral_eq_natCast_app] at h
  rw [h, eventualGraph_eval]
  apply exists_congr
  intro s
  have hreordered : Semiformula.Evalb ![s, (v : M), input, output]
      (evalnCertificateFormula : ArithmeticSemisentence 4) ↔
      evalnGraphFormula.val.Evalb ![output + 1, s, (v : M), input] := by
    change Semiformula.Evalb ![s, (v : M), input, output]
        (evalnCertificateFormula : ArithmeticSemisentence 4) ↔
      Semiformula.Evalb ![output + 1, s, (v : M), input] (code codeHistoryEvaluator)
    exact evalnCertificateFormula_eval_history_iff s (v : M) input output
  simpa only [numeral_eq_natCast_app, Matrix.cons_val_zero, Matrix.cons_val_one] using
    hreordered

/-- The program index in this theorem is deliberately a fixed Nat.
It is never instantiated by a free model-valued program variable. -/
theorem standard_stage_persist (v : ℕ) (s t input output : M) (hst : s ≤ t)
    (h : evalnGraphFormula.val.Evalb ![output + 1, s, (v : M), input]) :
    evalnGraphFormula.val.Evalb ![output + 1, t, (v : M), input] := by
  exact (evalnCertificateFormula_eval_history_iff t (v : M) input output).mp
    (evalnCertificateFormula_natCode_persist v s t input output hst
      ((evalnCertificateFormula_eval_history_iff s (v : M) input output).mpr h))

theorem identity_stage (s input : M) (hx : input < s) :
    evalnGraphFormula.val.Evalb ![input + 1, s, (Kleene.identityIndex : M), input] := by
  exact (evalnCertificateFormula_eval_history_iff s (Kleene.identityIndex : M) input input).mp
    (ConcreteWitnessGraphs.identity_computation s input hx)

theorem identity_stage_correct (s input output : M)
    (h : evalnGraphFormula.val.Evalb ![output + 1, s, (Kleene.identityIndex : M), input]) :
    output = input := by
  have hy := (standard_graph_stages_iff Kleene.identityIndex input output).mpr ⟨s, h⟩
  have hx := (standard_graph_stages_iff Kleene.identityIndex input input).mpr
    ⟨input + 1, identity_stage (input + 1) input (by simp)⟩
  exact output_unique (Kleene.identityIndex : M) input output input hy hx

noncomputable def templateIndex (v : ℕ) (a : M) : M :=
  compIndex (v : M) (pairIndex (constantIndex a) (Kleene.identityIndex : M))

end Models

def templateIndexGraph (v : ℕ) : 𝚺₁.Semisentence 2 :=
  let C := constantIndexGraph
  .mkSigma “o a. ∃ c p q, !C.val c a ∧ !pairDef.val p c !!(Kleene.identityIndex) ∧
    !pairDef.val q !!(v) (4 + 4 * p) ∧ o = 4 + 4 * q + 2”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance templatesLocalInstance4 : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance templatesLocalInstance5 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance templatesLocalInstance6 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance

@[simp] theorem templateIndexGraph_eval (v : ℕ) (o a : M) :
    (templateIndexGraph v).val.Evalb ![o, a] ↔ o = templateIndex v a := by
  simp [templateIndexGraph, templateIndex, compIndex, pairIndex, numeral_eq_natCast_app]

instance templateIndex_defined (v : ℕ) :
    𝚺₁-Function₁ (templateIndex v : M → M) via templateIndexGraph v := .mk fun w => by
  have hw : ![w 0, w 1] = w := (Matrix.fun_eq_vec_two w).symm
  simpa only [hw, Fin.succ_zero_eq_one] using
    templateIndexGraph_eval v (w 0) (w 1)
instance templateIndex_definable (v : ℕ) : 𝚺₁-Function₁ (templateIndex v : M → M) :=
  (templateIndex_defined v).to_definable
instance templateIndex_definable' (v : ℕ) (Γ m) : Γ-[m + 1]-Function₁ (templateIndex v : M → M) :=
  (templateIndex_definable v).of_sigmaOne

/-- Soundness applies to every successful stage of the newly generated
program, with no sufficient-fuel premise. -/
theorem template_stage_sound (v : ℕ) (a s input output : M)
    (h : evalnGraphFormula.val.Evalb ![output + 1, s, templateIndex v a, input]) :
    graph.val.Evalb ![(v : M), ⟪a, input⟫, output] := by
  rw [templateIndex, composition_stage_iff] at h
  obtain ⟨middle, hPair, hV⟩ := h
  obtain ⟨left, right, hLeft, hRight, hMiddle⟩ :=
    (pairing_stage_iff s (constantIndex a) (Kleene.identityIndex : M) input middle).mp hPair
  have hL : left = a := constantIndex_correct a s input left hLeft
  have hR : right = input := identity_stage_correct s input right hRight
  rw [hL, hR] at hMiddle
  rw [hMiddle] at hV
  exact (standard_graph_stages_iff v ⟪a, input⟫ output).mpr ⟨s, hV⟩

/-- This is an actual s-m-n parameter compiler for the fixed template.
Its parameter and its ordinary input range over the entire PA model. -/
theorem templateIndex_graph (v : ℕ) (a input output : M) :
    graph.val.Evalb ![templateIndex v a, input, output] ↔
      graph.val.Evalb ![(v : M), ⟪a, input⟫, output] := by
  constructor
  · intro h
    obtain ⟨t, ht, ho⟩ := (graph_iff_trace (templateIndex v a) input output).mp h
    have he := ((traceFormula_eval (templateIndex v a) input t).mp ht).1
    rw [ho] at he
    exact template_stage_sound v a (π₁ t) input output
      ((stageFormula_eval (output + 1) (π₁ t) (templateIndex v a) input).mpr he.symm)
  · intro h
    obtain ⟨s, hV⟩ := (standard_graph_stages_iff v ⟪a, input⟫ output).mp h
    let fuel := s + a + input + 1
    have hs : s ≤ fuel := by simp [fuel, add_assoc]
    have ha : a < fuel := by simp [fuel, add_assoc, add_left_comm]
    have hx : input < fuel := by
      have hle : input ≤ (s + a) + input := by
        simpa only [zero_add] using
          add_le_add_left (FFL.FirstOrder.Arithmetic.zero_le (s + a)) input
      exact lt_of_le_of_lt hle (by simp [fuel])
    have hC := constantIndex_sufficient_stage a fuel input ha hx
    have hI := identity_stage fuel input hx
    have hP := (pairing_stage_iff fuel (constantIndex a) (Kleene.identityIndex : M)
      input ⟪a, input⟫).mpr ⟨a, input, hC, hI, rfl⟩
    have hV' := standard_stage_persist v s fuel ⟪a, input⟫ output hs hV
    have hRaw : evalnGraphFormula.val.Evalb ![output + 1, fuel, templateIndex v a, input] :=
      (composition_stage_iff fuel (v : M)
        (pairIndex (constantIndex a) (Kleene.identityIndex : M)) input output).mpr
          ⟨⟪a, input⟫, hP, hV'⟩
    exact graph_of_consistent_stage (templateIndex v a) input output
      (fun r z hz => output_unique (v : M) ⟪a, input⟫ z output
        (template_stage_sound v a r input z hz) h) fuel hRaw

end Models
end CategoricalEssentialIncompleteness.V46.UniformTrace
