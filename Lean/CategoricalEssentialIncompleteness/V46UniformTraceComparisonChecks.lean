/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceComparison

/-! # Checks for the uniform trace construction -/

@[expose] public section

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.ComparisonChecks

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalRiceShapiro.Evaluator
open CategoricalEssentialIncompleteness.V46.UniformTrace

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance traceChecksSigma : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺 1) inferInstance
example (f e:ℕ) : FailureOfComposition.ProofSearch.Uniform 𝗣𝗔
    (FailureOfComposition.ConcreteEvaluator.eventualGraph (compose f e))
    (FailureOfComposition.ConcreteEvaluator.eventualGraph
      (CategoricalRiceShapiro.PartialRecursive.canonicalPartrecCompIndex f e)) :=
  compose_production_PA f e

end
end CategoricalEssentialIncompleteness.V46.UniformTrace.ComparisonChecks
