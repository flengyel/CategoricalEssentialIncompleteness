/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceConstants

/-! # Checks for the uniform trace construction -/

@[expose] public section

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.ConstantsChecks

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalRiceShapiro.Evaluator
open CategoricalEssentialIncompleteness.V46.UniformTrace

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance traceChecksSigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺 1) inferInstance
example (a s x y : M)
    (h : evalnGraphFormula.val.Evalb ![y+1,s,constantIndex a,x]) : y=a :=
  constantIndex_correct a s x y h
example (a s x : M) (ha:a<s) (hx:x<s) :
    evalnGraphFormula.val.Evalb ![a+1,s,constantIndex a,x] :=
  constantIndex_sufficient_stage a s x ha hx
example (a x y : M) : graph.val.Evalb ![constantIndex a,x,y] ↔ y=a := constantIndex_graph a x y
example : 𝗣𝗔 ⊢ constantIndexTotalSentence := constantIndex_totality_PA

end
end CategoricalEssentialIncompleteness.V46.UniformTrace.ConstantsChecks
