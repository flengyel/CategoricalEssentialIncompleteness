import CategoricalEssentialIncompleteness.V46UniformTraceBuilders

/-! # Checks for the uniform trace construction -/

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.BuildersChecks

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalRiceShapiro.Evaluator
open CategoricalEssentialIncompleteness.V46.UniformTrace

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance traceChecksSigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺 1) inferInstance
example (e a x y:M) : graph.val.Evalb ![specialize e a,x,y] ↔
    graph.val.Evalb ![e,ExponentialPairing.code a x,y] := specialize_eval e a x y
example (f e x z:M) : graph.val.Evalb ![compose f e,x,z] ↔
    ∃ y:M,graph.val.Evalb ![e,x,y] ∧ graph.val.Evalb ![f,y,z] := compose_eval f e x z
example : 𝗣𝗔 ⊢ compositionSentence := composition_PA
example : 𝗣𝗔 ⊢ specializationSentence := specialization_PA
example : 𝗣𝗔 ⊢ buildersTotalitySentence := builders_totality_PA

end
end CategoricalEssentialIncompleteness.V46.UniformTrace.BuildersChecks
