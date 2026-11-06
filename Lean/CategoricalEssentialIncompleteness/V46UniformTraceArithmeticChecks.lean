import CategoricalEssentialIncompleteness.V46UniformTraceArithmetic

/-! # Checks for the uniform trace construction -/

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.ArithmeticChecks

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalRiceShapiro.Evaluator
open CategoricalEssentialIncompleteness.V46.UniformTrace

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance traceChecksSigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺 1) inferInstance
example : 𝗣𝗔 ⊢ primitiveTraceGraphSentence := primitive_trace_graph_PA
example : 𝗣𝗔 ⊢ functionalitySentence := functionality_PA
example : 𝗣𝗔 ⊢ universalSentence := universal_PA
example : 𝗣𝗔 ⊢ specializationSentence := specialization_PA
example : 𝗣𝗔 ⊢ compositionSentence := composition_PA
example (e:ℕ) : 𝗣𝗔 ⊢ specializerSectionSentence e := specializerSection_PA e

end
end CategoricalEssentialIncompleteness.V46.UniformTrace.ArithmeticChecks
