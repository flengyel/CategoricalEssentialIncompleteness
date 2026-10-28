/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.GeneratedWitnessGraphs

/-!
# The first-success graph of the concrete evaluator

The code `canonicalEvalnCode` searches for the first stage at which the
production history evaluator has a positive output, then subtracts one from
that output.  Its arithmetic graph is therefore the first-success presentation
of the same partial function represented by `ConcreteEvaluator.eventualGraph`.

The comparison is proved over every model of PA at a fixed external program
index.  Its reverse direction uses the existing least-stage normalization, so
no least-number or persistence argument is repeated here.
-/

@[expose] public section

set_option autoImplicit false

open Nat Nat.ArithPart₁
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition

open ProofSearch ConcreteEvaluator GeneratedWitnessGraphs

/-- Search for the first stage whose production history output is positive. -/
def firstSuccessfulEvalnStageCode : Code 2 :=
  codeRfindPos codeHistoryEvaluator

/-- Run the history evaluator at its first successful stage and decode its
successor-coded output. -/
def canonicalEvalnCode : Code 2 :=
  codeBind firstSuccessfulEvalnStageCode
    (codeSub codeHistoryEvaluator (codeConst (n := 3) 1))

/-- The three-place arithmetic graph of `canonicalEvalnCode`, with arguments
ordered as program index, input, and output. -/
def canonicalPartrecGraphFormula : 𝚺₁.Semisentence 3 :=
  (HierarchySymbol.Semiformula.mkSigma (code canonicalEvalnCode)
      (code_sigma_one canonicalEvalnCode)).rew
    (Rew.subst ![
      (#2 : ArithmeticSemiterm Empty 3),
      (#0 : ArithmeticSemiterm Empty 3),
      (#1 : ArithmeticSemiterm Empty 3)])

/-- Evaluation of the graph formula is evaluation of the underlying code with
the output moved to the leading graph coordinate. -/
theorem canonicalPartrecGraphFormula_eval_iff
    {M : Type*} [ORingStructure M] (qCode u y : M) :
    Semiformula.Evalb ![qCode, u, y]
        (↑canonicalPartrecGraphFormula : ArithmeticSemisentence 3) ↔
      Semiformula.Evalb ![y, qCode, u] (code canonicalEvalnCode) := by
  simp [canonicalPartrecGraphFormula, Semiformula.eval_rew,
    Function.comp_def, Matrix.fun_eq_vec_three]

/-- Unfolding the binding code exposes its selected stage. -/
theorem canonicalPartrecGraphFormula_eval_stage_bind_iff
    {M : Type*} [ORingStructure M] (qCode u y : M) :
    Semiformula.Evalb ![qCode, u, y]
        (↑canonicalPartrecGraphFormula : ArithmeticSemisentence 3) ↔
      ∃ s : M,
        Semiformula.Evalb ![s, qCode, u]
            (code firstSuccessfulEvalnStageCode) ∧
          Semiformula.Evalb ![y, s, qCode, u]
            (code (codeSub codeHistoryEvaluator (codeConst (n := 3) 1))) := by
  rw [canonicalPartrecGraphFormula_eval_iff]
  simpa only [canonicalEvalnCode] using
    (eval_codeBind_iff firstSuccessfulEvalnStageCode
      (codeSub codeHistoryEvaluator (codeConst (n := 3) 1)) y ![qCode, u])

/-- The stage-search code selects exactly a positive history value preceded by
literal zero history values. -/
theorem firstSuccessfulEvalnStageCode_eval_iff
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (s qCode u : M) :
    Semiformula.Evalb ![s, qCode, u]
        (code firstSuccessfulEvalnStageCode) ↔
      ((∃ a : M, 0 < a ∧
          Semiformula.Evalb ![a, s, qCode, u] (code codeHistoryEvaluator)) ∧
        ∀ t : M, t < s →
          Semiformula.Evalb ![0, t, qCode, u] (code codeHistoryEvaluator)) := by
  simpa only [firstSuccessfulEvalnStageCode] using
    (eval_codeRfindPos_iff codeHistoryEvaluator s ![qCode, u])

/-- The positive value selected by the stage search is precisely a successful
production certificate, while every earlier history value is literally zero. -/
theorem firstSuccessfulEvalnStageCode_eval_certificate_iff
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (s qCode u : M) :
    Semiformula.Evalb ![s, qCode, u]
        (code firstSuccessfulEvalnStageCode) ↔
      ((∃ y : M, Semiformula.Evalb ![s, qCode, u, y]
          (evalnCertificateFormula : ArithmeticSemisentence 4)) ∧
        ∀ t : M, t < s →
          Semiformula.Evalb ![0, t, qCode, u] (code codeHistoryEvaluator)) := by
  rw [firstSuccessfulEvalnStageCode_eval_iff]
  constructor
  · rintro ⟨⟨a, ha, hhist⟩, hzero⟩
    obtain ⟨y, rfl⟩ := eq_succ_of_pos ha
    exact ⟨⟨y, (evalnCertificateFormula_eval_history_iff s qCode u y).mpr hhist⟩,
      hzero⟩
  · rintro ⟨⟨y, hcert⟩, hzero⟩
    exact ⟨⟨y + 1, by simp,
      (evalnCertificateFormula_eval_history_iff s qCode u y).mp hcert⟩, hzero⟩

/-- At a selected stage, subtracting one from the history value returns exactly
the output named by the production certificate. -/
theorem selectedStageSub_eval_certificate_iff
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (s qCode u y : M)
    (hstage : Semiformula.Evalb ![s, qCode, u]
      (code firstSuccessfulEvalnStageCode)) :
    Semiformula.Evalb ![y, s, qCode, u]
        (code (codeSub codeHistoryEvaluator (codeConst (n := 3) 1))) ↔
      Semiformula.Evalb ![s, qCode, u, y]
        (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  obtain ⟨⟨x, hcertx⟩, -⟩ :=
    (firstSuccessfulEvalnStageCode_eval_certificate_iff s qCode u).mp hstage
  have hhistx : Semiformula.Evalb ![x + 1, s, qCode, u]
      (code codeHistoryEvaluator) :=
    (evalnCertificateFormula_eval_history_iff s qCode u x).mp hcertx
  have hone : Semiformula.Evalb ![1, s, qCode, u]
      (code (codeConst (n := 3) 1)) := by
    simpa using eval_codeConst (M := M) 1 ![s, qCode, u]
  have hsubx : Semiformula.Evalb ![x, s, qCode, u]
      (code (codeSub codeHistoryEvaluator (codeConst (n := 3) 1))) := by
    simpa using eval_codeSub codeHistoryEvaluator (codeConst (n := 3) 1)
      (x + 1) 1 ![s, qCode, u] hhistx hone
  constructor
  · intro hsuby
    have hyx : y = x := eval_unique hsuby hsubx
    rw [hyx]
    exact hcertx
  · intro hcerty
    have hyx : y = x := by
      apply add_right_cancel
      exact eval_unique
        ((evalnCertificateFormula_eval_history_iff s qCode u y).mp hcerty)
        hhistx
    rw [hyx]
    exact hsubx

/-- The production first-success graph consists of a successful certificate at
some stage and literal zero history values at every earlier stage. -/
theorem canonicalPartrecGraphFormula_eval_certificate_iff
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
    (qCode u y : M) :
    Semiformula.Evalb ![qCode, u, y]
        (↑canonicalPartrecGraphFormula : ArithmeticSemisentence 3) ↔
      ∃ s : M,
        Semiformula.Evalb ![s, qCode, u, y]
            (evalnCertificateFormula : ArithmeticSemisentence 4) ∧
          ∀ t : M, t < s →
            Semiformula.Evalb ![0, t, qCode, u]
              (code codeHistoryEvaluator) := by
  rw [canonicalPartrecGraphFormula_eval_stage_bind_iff]
  constructor
  · rintro ⟨s, hs, hsub⟩
    refine ⟨s, (selectedStageSub_eval_certificate_iff s qCode u y hs).mp hsub, ?_⟩
    exact ((firstSuccessfulEvalnStageCode_eval_certificate_iff s qCode u).mp hs).2
  · rintro ⟨s, hcert, hzero⟩
    have hs : Semiformula.Evalb ![s, qCode, u]
        (code firstSuccessfulEvalnStageCode) :=
      (firstSuccessfulEvalnStageCode_eval_certificate_iff s qCode u).mpr
        ⟨⟨y, hcert⟩, hzero⟩
    exact ⟨s, hs, (selectedStageSub_eval_certificate_iff s qCode u y hs).mpr hcert⟩

/-- At every fixed standard program index, the first-success formula and the
production existential-stage graph agree in every model of PA. -/
theorem canonicalPartrecGraphFormula_eval_iff_eventualGraph
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q : ℕ) (u y : M) :
    Semiformula.Evalb
        ![(ORingStructure.numeral q : M), u, y]
        (↑canonicalPartrecGraphFormula : ArithmeticSemisentence 3) ↔
      (ConcreteEvaluator.eventualGraph q).val.Evalb ![u, y] := by
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  constructor
  · intro h
    obtain ⟨s, hcert, -⟩ :=
      (canonicalPartrecGraphFormula_eval_certificate_iff
        (ORingStructure.numeral q : M) u y).mp h
    exact (eventualGraph_eval q _).mpr ⟨s, hcert⟩
  · intro h
    obtain ⟨s, hleast, hstage⟩ := leastGraph_exists q u y h
    refine (canonicalPartrecGraphFormula_eval_certificate_iff
      (ORingStructure.numeral q : M) u y).mpr ⟨s, ?_, ?_⟩
    · simpa only [numeral_eq_natCast_app] using
        (stageGraph_eval q s u y).mp hstage
    · intro t ht
      have hfailure := ((leastGraph_eval q u s).mp hleast).2 t ht
      simpa only [numeral_eq_natCast_app] using
        (failureGraph_eval q t u).mp hfailure

/-- The fixed-index specialization of the three-place first-success formula. -/
def firstSuccessGraph (q : ℕ) : Graph :=
  canonicalPartrecGraphFormula.rew
    (Rew.subst ![
      (↑q : ArithmeticSemiterm Empty 2),
      (#0 : ArithmeticSemiterm Empty 2),
      (#1 : ArithmeticSemiterm Empty 2)])

theorem firstSuccessGraph_val (q : ℕ) :
    (firstSuccessGraph q).val =
      canonicalPartrecGraphFormula.val/[
        (↑q : ArithmeticSemiterm Empty 2),
        (#0 : ArithmeticSemiterm Empty 2),
        (#1 : ArithmeticSemiterm Empty 2)] := by
  simp [firstSuccessGraph]

@[simp] theorem firstSuccessGraph_eval
    {M : Type*} [ORingStructure M] (q : ℕ) (u y : M) :
    (firstSuccessGraph q).val.Evalb ![u, y] ↔
      Semiformula.Evalb ![(ORingStructure.numeral q : M), u, y]
        (↑canonicalPartrecGraphFormula : ArithmeticSemisentence 3) := by
  simp [firstSuccessGraph]

/-- PA proves the uniform equivalence between the fixed-index first-success
graph and the production existential-stage graph. -/
theorem firstSuccessGraph_uniform_eventualGraph (q : ℕ) :
    Uniform 𝗣𝗔 (firstSuccessGraph q) (eventualGraph q) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, uniformSentence_eval]
  intro u y
  rw [firstSuccessGraph_eval]
  exact canonicalPartrecGraphFormula_eval_iff_eventualGraph q u y

end FailureOfComposition
