/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceFlags

/-! # Selecting a first trace from consistent stage computations -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalRiceShapiro.Evaluator

namespace CategoricalEssentialIncompleteness.V46.UniformTrace
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance stageSelectionLocalInstance1 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance stageSelectionLocalInstance2 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance

/-- A successful stage yields the first-success graph when every successful stage has the
same output. This lemma assumes neither persistence nor a first-success computation;
the least stage is constructed internally. -/
theorem graph_of_consistent_stage (e x y : M)
    (hsound : ∀ s z : M, evalnGraphFormula.val.Evalb ![z + 1, s, e, x] → z = y)
    (s : M) (hs : evalnGraphFormula.val.Evalb ![y + 1, s, e, x]) :
    graph.val.Evalb ![e, x, y] := by
  have hdef : 𝚺₁.DefinablePred (fun r : M => 0 < stageValue r e x) := by definability
  have hpos : 0 < stageValue s e x := by
    rw [← (stageFormula_eval (y + 1) s e x).mp hs]
    simp
  obtain ⟨first, hfirst, hleast⟩ := InductionOnHierarchy.least_number 𝚺 1 hdef hpos
  obtain ⟨z, hz⟩ := eq_succ_of_pos hfirst
  have hraw : evalnGraphFormula.val.Evalb ![z + 1, first, e, x] :=
    (stageFormula_eval (z + 1) first e x).mpr hz.symm
  have hzy : z = y := hsound first z hraw
  have hearlier (r : M) (hr : r < first) : stageValue r e x = 0 := by
    exact le_antisymm (not_lt.mp (hleast r hr)) (FFL.FirstOrder.Arithmetic.zero_le _)
  apply (graph_iff_trace e x y).mpr
  refine ⟨⟪first, y⟫, ?_, by simp [out]⟩
  apply (traceFormula_eval e x ⟪first, y⟫).mpr
  constructor
  · simpa only [pi₁_pair, out, pi₂_pair, hzy] using hz
  · intro r hr
    exact hearlier r (by simpa only [pi₁_pair] using hr)

end Models
end CategoricalEssentialIncompleteness.V46.UniformTrace
