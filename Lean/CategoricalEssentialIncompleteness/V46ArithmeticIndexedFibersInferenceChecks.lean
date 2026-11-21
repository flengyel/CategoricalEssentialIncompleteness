/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersInference


/-! # Inference base change from premise and conclusion diagrams -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers.RuleBaseChange
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {F F' : D} {N : ℕ} (j : F' ⟶ F)
variable (R' : RulePresentation F' N) (R : RulePresentation F N) (h : Data j R' R)
example (Q : Over F) (i : Fin (N+1)) :
    IsPullback (inputComponent j R' R h Q i) (R'.ruleConclusion ((Over.pullback j).obj Q) i)
      (R.ruleConclusion Q i) j := component_isPullback j R' R h Q i
example : R.inference ⋙ Over.pullback j ≅ Over.pullback j ⋙ R'.inference := comparison j R' R h
example (Q : Over F) :
    (componentIso j R' R h Q).hom.left ≫ pullback.fst (R.inference.obj Q).hom j =
      input j R' R h Q := componentIso_input j R' R h Q
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers.RuleBaseChange
