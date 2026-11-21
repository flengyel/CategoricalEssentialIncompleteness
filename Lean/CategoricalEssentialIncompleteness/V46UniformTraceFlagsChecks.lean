/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceFlags

/-! # Checks for bounded earlier-stage flags -/

@[expose] public section

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.FlagsChecks

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalRiceShapiro.ArithmeticCode
open CategoricalEssentialIncompleteness.V46.UniformTrace

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance checkSigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance checkOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺 1) inferInstance

example (s e x : M) : earlier s e x = 1 ↔ ∀ r < s, stageValue r e x = 0 :=
  earlier_one_iff s e x

example (s e x : M) : ∃ flag : M,
    Semiformula.Evalb ![flag, s, e, x] (code earlierCode) := earlier_exists s e x

end
end CategoricalEssentialIncompleteness.V46.UniformTrace.FlagsChecks
