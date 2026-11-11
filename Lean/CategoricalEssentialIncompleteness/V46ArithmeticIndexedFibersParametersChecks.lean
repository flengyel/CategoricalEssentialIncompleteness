/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersParameters


/-! # Statement checks in `V46ArithmeticIndexedFibersParametersChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {E F P : D} (R : RulePresentation (E ⨯ F) 2) (m : P ⟶ E)
example (i : Fin 3) :
    IsPullback (pullback.fst (R.conclusion i ≫ prod.fst) m)
      (parameterRuleConclusion R m i) (R.conclusion i) (prod.map m (𝟙 F)) := parameterRuleSquare R m i
example (h : ParameterPreserving R) :
    R.inference ⋙ Over.pullback (prod.map m (𝟙 F)) ≅
      Over.pullback (prod.map m (𝟙 F)) ⋙ (parameterRules R m).inference := parameterInferenceComparison R m h
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
