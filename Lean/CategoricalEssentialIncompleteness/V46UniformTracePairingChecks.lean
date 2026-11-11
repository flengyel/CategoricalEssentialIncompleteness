/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTracePairing

/-! # Checks for the uniform trace construction -/

@[expose] public section

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.PairingChecks

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalRiceShapiro.Evaluator
open CategoricalEssentialIncompleteness.V46.UniformTrace

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance traceChecksSigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺 1) inferInstance
example (s f e x y : M) :
    evalnGraphFormula.val.Evalb ![y+1,s,ProgramIndices.pairIndex f e,x] ↔
      ∃ a b : M, evalnGraphFormula.val.Evalb ![a+1,s,f,x] ∧
        evalnGraphFormula.val.Evalb ![b+1,s,e,x] ∧ y=⟪a,b⟫ := pairing_stage_iff s f e x y

end
end CategoricalEssentialIncompleteness.V46.UniformTrace.PairingChecks
