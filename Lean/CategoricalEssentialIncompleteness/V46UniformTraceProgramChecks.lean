import CategoricalEssentialIncompleteness.V46UniformTraceProgram

/-! # Checks for the uniform trace construction -/

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.ProgramChecks

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.UniformTrace

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance checkSigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance checkOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺 1) inferInstance

example (e x y : M) : graph.val.Evalb ![e, x, y] ↔ ∃ t : M,
    traceProgramGraph.val.Evalb ![(1 : M), e, x, t] ∧ out t = y := graph_iff_program_trace e x y

example : 𝗣𝗔 ⊢ traceProgramComparisonSentence := traceProgram_comparison_PA
example : 𝗣𝗔 ⊢ primitiveTraceGraphSentence := primitive_trace_graph_PA

end
end CategoricalEssentialIncompleteness.V46.UniformTrace.ProgramChecks
