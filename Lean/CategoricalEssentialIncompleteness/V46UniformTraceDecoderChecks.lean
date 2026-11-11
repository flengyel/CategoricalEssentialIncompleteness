/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceDecoder

/-! # Checks for the uniform trace construction -/

@[expose] public section

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.DecoderChecks

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode
open CategoricalEssentialIncompleteness.V46.UniformTrace.ProgramIndices

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance checkSigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance checkOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺 1) inferInstance

example (f g : M) : tag (compIndex f g) = 5 := tag_compIndex f g
example (f g : M) : payload (compIndex f g) = ⟪f, g⟫ := payload_compIndex f g

example (q : M) : Semiformula.Evalb ![payload q, q]
    (code (codePartrecPayload (Code.proj (0 : Fin 1)))) :=
  payload_value _ q ![q] ((eval_proj_iff _ _ _).mpr rfl)

example (q : M) : Semiformula.Evalb ![tag q, q]
    (code (codePartrecTag (Code.proj (0 : Fin 1)))) :=
  tag_value _ q ![q] ((eval_proj_iff _ _ _).mpr rfl)

end
end CategoricalEssentialIncompleteness.V46.UniformTrace.DecoderChecks
