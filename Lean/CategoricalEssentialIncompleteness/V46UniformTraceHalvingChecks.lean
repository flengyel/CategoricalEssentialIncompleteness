/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceHalving

/-! # Checks for the uniform trace construction -/

@[expose] public section

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.HalvingChecks

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode
open CategoricalEssentialIncompleteness.V46.UniformTrace

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance checkSigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance checkOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺 1) inferInstance

example (a : M) : Semiformula.Evalb ![a / 2, a] (code codeDiv2Unary) := half_unary_value a

example {n : ℕ} (A : Code n) (a o : M) (v : Fin n → M)
    (h : Semiformula.Evalb (a :> v) (code A)) :
    Semiformula.Evalb (o :> v) (code (codeDiv2 A)) ↔ o = a / 2 := half_value_iff A a o v h

end
end CategoricalEssentialIncompleteness.V46.UniformTrace.HalvingChecks
