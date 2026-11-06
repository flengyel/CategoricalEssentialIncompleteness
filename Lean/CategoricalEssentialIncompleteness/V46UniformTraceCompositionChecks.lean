import CategoricalEssentialIncompleteness.V46UniformTraceComposition

/-! # Checks for the uniform trace construction -/

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.CompositionChecks

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalRiceShapiro.Evaluator
open CategoricalEssentialIncompleteness.V46.UniformTrace

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance traceChecksSigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺 1) inferInstance
example (s f e x y : M) :
    evalnGraphFormula.val.Evalb ![y+1,s,ProgramIndices.compIndex f e,x] ↔
      ∃ z : M, evalnGraphFormula.val.Evalb ![z+1,s,e,x] ∧
        evalnGraphFormula.val.Evalb ![y+1,s,f,z] := composition_stage_iff s f e x y

end
end CategoricalEssentialIncompleteness.V46.UniformTrace.CompositionChecks
