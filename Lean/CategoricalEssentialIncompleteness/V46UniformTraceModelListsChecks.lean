import CategoricalEssentialIncompleteness.V46UniformTraceModelLists

/-! # Checks for the uniform trace construction -/

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.ModelListsChecks

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode
open CategoricalEssentialIncompleteness.V46.UniformTrace.ModelLists

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance checkSigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance checkOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance
local instance modelListChecksLt : DecidableLT M := Classical.decRel _

example (l i : M) : drop l i = 0 ↔ len l ≤ i := drop_eq_zero_iff l i

example (l : M) : Semiformula.Evalb ![len l, l]
    (code (codeListLength (Code.proj (0 : Fin 1)))) :=
  length_value _ l ![l] ((eval_proj_iff _ _ _).mpr rfl)

example (l i : M) : Semiformula.Evalb ![if i < len l then nth l i + 1 else 0, l, i]
    (code (codeListGet? (Code.proj (0 : Fin 2)) (Code.proj 1))) :=
  get_value _ _ l i ![l, i] ((eval_proj_iff _ _ _).mpr rfl) ((eval_proj_iff _ _ _).mpr rfl)

end
end CategoricalEssentialIncompleteness.V46.UniformTrace.ModelListsChecks
