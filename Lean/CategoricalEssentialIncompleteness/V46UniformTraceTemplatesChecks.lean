import CategoricalEssentialIncompleteness.V46UniformTraceTemplates

/-! # Checks for the uniform trace construction -/

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.TemplatesChecks

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalRiceShapiro.Evaluator
open CategoricalEssentialIncompleteness.V46.UniformTrace

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance traceChecksSigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺 1) inferInstance
example (v:ℕ) (a x y:M) : graph.val.Evalb ![templateIndex v a,x,y] ↔
    graph.val.Evalb ![(v:M),⟪a,x⟫,y] := templateIndex_graph v a x y

end
end CategoricalEssentialIncompleteness.V46.UniformTrace.TemplatesChecks
