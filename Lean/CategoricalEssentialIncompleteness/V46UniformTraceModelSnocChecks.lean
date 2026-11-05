import CategoricalEssentialIncompleteness.V46UniformTraceModelSnoc

/-! # Checks for the uniform trace construction -/

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.ModelSnocChecks

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode
open CategoricalEssentialIncompleteness.V46.UniformTrace.ModelLists

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance checkSigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance checkOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺 1) inferInstance

example (l x : M) : Semiformula.Evalb ![concat l x, l, x]
    (code (codeListSnoc (Code.proj (0 : Fin 2)) (Code.proj 1))) :=
  snoc_value _ _ l x ![l, x] ((eval_proj_iff _ _ _).mpr rfl) ((eval_proj_iff _ _ _).mpr rfl)

end
end CategoricalEssentialIncompleteness.V46.UniformTrace.ModelSnocChecks
