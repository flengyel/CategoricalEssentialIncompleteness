import CategoricalEssentialIncompleteness.V46UniformTraceStageSelection

/-! # Checks for the uniform trace construction -/

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.StageSelectionChecks

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalRiceShapiro.Evaluator
open CategoricalEssentialIncompleteness.V46.UniformTrace

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance traceChecksSigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺 1) inferInstance
example (e x y s : M)
    (hs : evalnGraphFormula.val.Evalb ![y+1,s,e,x])
    (h : ∀ r z : M, evalnGraphFormula.val.Evalb ![z+1,r,e,x] → z=y) :
    graph.val.Evalb ![e,x,y] := graph_of_consistent_stage e x y h s hs

end
end CategoricalEssentialIncompleteness.V46.UniformTrace.StageSelectionChecks
