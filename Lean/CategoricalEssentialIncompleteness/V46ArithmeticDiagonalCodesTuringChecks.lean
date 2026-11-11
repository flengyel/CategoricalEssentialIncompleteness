/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodesTuring

/-! # Exact statement checks for the arithmetic diagonal construction -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedTuringMorphism
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalCodes.TuringChecks
example : isTotal adapter := adapter_total
example : PCategoryStruct.nearProd_map adapter (𝟙 (omegaObject 𝗣𝗔)) ≫ sourceTau =
    typedTau 𝗣𝗔 := adapter_factorization
example : RecursionCategory.IsTuringMorphism sourceTau := sourceTau_isTuring
example : Inseparable a0 a1 := source_pair_inseparable
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (q x y : M) :
    UniformTrace.graph.val.Evalb
      ![UniformTrace.specialize (oldTauTemplateIndex : M) q,x,y] ↔
      (FailureOfComposition.ConcreteEvaluator.eventualGraph tauIndex).val.Evalb
        ![pair q x,y] := adapter_application q x y
end CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalCodes.TuringChecks
