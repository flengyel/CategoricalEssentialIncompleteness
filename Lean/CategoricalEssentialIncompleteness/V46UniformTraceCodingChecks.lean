/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceCoding


/-! # First-success traces with a variable program index -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalRiceShapiro.Evaluator
open CategoricalEssentialIncompleteness.V46.UniformTrace

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.CodingChecks
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (s e x : M) : ∃! o : M, evalnGraphFormula.val.Evalb ![o, s, e, x] :=
  stage_total_unique s e x

example (e x y : M) : graph.val.Evalb ![e, x, y] ↔
    ∃ t : M, traceFormula.val.Evalb ![e, x, t] ∧ out t = y := graph_iff_trace e x y

example : 𝗣𝗔 ⊢ stageTotalitySentence := stage_totality_PA
example : 𝗣𝗔 ⊢ traceComparisonSentence := trace_comparison_PA
example : Nat.Primrec (out : ℕ → ℕ) := out_natPrimrec
end CategoricalEssentialIncompleteness.V46.UniformTrace.CodingChecks
