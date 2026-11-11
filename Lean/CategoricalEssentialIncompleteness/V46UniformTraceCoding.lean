/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTrace
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPrimitiveParser

/-! # A literal first-success trace code, uniform in the internal program index

The trace code is the pair of its stage and displayed output. Its arithmetic
predicate checks the actual production history and every earlier stage. This
file proves the all-model PA graph comparison and the standard output-reader
certificate. The standard primitive-recursion certificate for the complete
trace predicate is a separate obligation; totality alone is insufficient.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator
open FailureOfComposition FailureOfComposition.ConcreteEvaluator

namespace CategoricalEssentialIncompleteness.V46.UniformTrace

/-- A trace records the least successful stage and its output, without
replacing a program index by an external standard numeral. -/
def traceFormula : 𝚺₁.Semisentence 3 :=
  let H := evalnGraphFormula
  .mkSigma “e x t. ∃ s y, !pi₁Def.val s t ∧ !pi₂Def.val y t ∧
    !H.val (y + 1) s e x ∧ ∀ r < s, !H.val 0 r e x”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- This is the actual total fixed-stage evaluator, selected from its
proved production graph. No totality premise is supplied by a caller. -/
noncomputable def stageValue (s e x : M) : M :=
  Classical.choose (eval_codeHistoryEvaluator_exists s e x)

theorem stageValue_spec (s e x : M) :
    Semiformula.Evalb ![stageValue s e x, s, e, x] (code codeHistoryEvaluator) :=
  Classical.choose_spec (eval_codeHistoryEvaluator_exists s e x)

@[simp] theorem stageFormula_eval (o s e x : M) :
    evalnGraphFormula.val.Evalb ![o, s, e, x] ↔ o = stageValue s e x := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  change Semiformula.Evalb ![o, s, e, x] (code codeHistoryEvaluator) ↔ _
  constructor
  · intro h
    exact eval_unique h (stageValue_spec s e x)
  · intro h
    subst o
    exact stageValue_spec s e x

theorem stage_total_unique (s e x : M) :
    ∃! o : M, evalnGraphFormula.val.Evalb ![o, s, e, x] := by
  refine ⟨stageValue s e x, (stageFormula_eval _ s e x).mpr rfl, ?_⟩
  intro o ho
  exact (stageFormula_eval o s e x).mp ho

/-- The output reader keeps the literal second coordinate of a trace. -/
noncomputable def out (t : M) : M := π₂ t

@[simp] theorem traceFormula_eval (e x t : M) :
    traceFormula.val.Evalb ![e, x, t] ↔
      stageValue (π₁ t) e x = out t + 1 ∧
        ∀ r < π₁ t, stageValue r e x = 0 := by
  simp [traceFormula, out, eq_comm]

/-- The same three-place production graph has a trace presentation at
every internal index, input and output, including nonstandard elements. -/
theorem graph_iff_trace (e x y : M) :
    graph.val.Evalb ![e, x, y] ↔ ∃ t : M,
      traceFormula.val.Evalb ![e, x, t] ∧ out t = y := by
  change canonicalPartrecGraphFormula.val.Evalb ![e, x, y] ↔ _
  rw [canonicalPartrecGraphFormula_eval_certificate_iff]
  constructor
  · rintro ⟨s, hs, hearlier⟩
    refine ⟨⟪s, y⟫, ?_, by simp [out]⟩
    apply (traceFormula_eval e x ⟪s, y⟫).mpr
    constructor
    · have h := (evalnCertificateFormula_eval_history_iff s e x y).mp hs
      have hf := (stageFormula_eval (y + 1) s e x).mp h
      simpa [out] using hf.symm
    · intro r hr
      have hr' : r < s := by simpa using hr
      exact ((stageFormula_eval 0 r e x).mp (hearlier r hr')).symm
  · rintro ⟨t, ht, hy⟩
    obtain ⟨hstage, hearlier⟩ := (traceFormula_eval e x t).mp ht
    refine ⟨π₁ t, ?_, ?_⟩
    · apply (evalnCertificateFormula_eval_history_iff (π₁ t) e x y).mpr
      apply (stageFormula_eval (y + 1) (π₁ t) e x).mpr
      rw [← hy]
      exact hstage.symm
    · intro r hr
      exact (stageFormula_eval 0 r e x).mpr (hearlier r hr).symm

end Models

def stageTotalitySentence : ArithmeticSentence :=
  let H := evalnGraphFormula
  “∀ s e x, ∃ o, !H.val o s e x ∧ ∀ w, !H.val w s e x → w = o”

theorem stage_totality_PA : 𝗣𝗔 ⊢ stageTotalitySentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simp [models_iff, stageTotalitySentence]

def traceComparisonSentence : ArithmeticSentence :=
  let G := graph
  let R := traceFormula
  “∀ e x y, !G.val e x y ↔ ∃ t, !R.val e x t ∧ !pi₂Def.val y t”

theorem trace_comparison_PA : 𝗣𝗔 ⊢ traceComparisonSentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have h := graph_iff_trace (M := M)
  simpa [models_iff, traceComparisonSentence, out, eq_comm] using h

/-- An actual standard primitive-recursion certificate for the output
reader. It is independent of the still separate trace-predicate certificate. -/
theorem out_primrec : Primrec (out : ℕ → ℕ) :=
  SyntacticSyntax.NatVectors.pi2_primrec

theorem out_natPrimrec : Nat.Primrec (out : ℕ → ℕ) :=
  Primrec.nat_iff.mp out_primrec

end CategoricalEssentialIncompleteness.V46.UniformTrace
