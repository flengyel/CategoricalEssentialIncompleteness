/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceModelHistory

/-! # Checks for the uniform trace construction -/

@[expose] public section

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.ModelHistoryChecks

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.UniformTrace
open ModelHistory

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance checkSigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance checkOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺 1) inferInstance

example (N k q x : M) (h : ⟪k, q⟫ < N) :
    lookup (history N) k q x = stageValue k q x := lookup_history_eq N k q x h

example (n m i : M) (h : n ≤ m) (hi : i < n) :
    nth (history m) i = nth (history n) i := history_nth_stable n m i h hi

end
end CategoricalEssentialIncompleteness.V46.UniformTrace.ModelHistoryChecks
