import CategoricalEssentialIncompleteness.V46UniformTraceSpecializers

/-! # Checks for the uniform trace construction -/

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.SpecializersChecks

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalRiceShapiro.Evaluator
open CategoricalEssentialIncompleteness.V46.UniformTrace

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance traceChecksSigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺 1) inferInstance
example (e:ℕ) (a p:M) : graph.val.Evalb ![(specializerSectionIndex e:M),a,p] ↔
    p=specialize (e:M) a := specializerSection_eval e a p
example (e:ℕ) : 𝗣𝗔 ⊢ specializerSectionTotalitySentence e := specializerSection_totality_PA e

end
end CategoricalEssentialIncompleteness.V46.UniformTrace.SpecializersChecks
