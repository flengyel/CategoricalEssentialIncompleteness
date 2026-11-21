/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersConstructors


/-! # Cartesian numeral comparison of the Hilbert rule signature -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
example (AxPA : Carrier) (e : ℕ) (i : Fin 3) :
    IsPullback (numeralRuleMap AxPA e i) ((singleRules AxPA e).conclusion i)
      ((ArithmeticIndexedFamily.rules AxPA).conclusion i)
      (fiberMap e ArithmeticIndexedFamily.formula) := numeralRuleConclusion AxPA e i
example (AxPA : Carrier) (e : ℕ) :
    (ArithmeticIndexedFamily.rules AxPA).inference ⋙
        Over.pullback (fiberMap e ArithmeticIndexedFamily.formula) ≅
      Over.pullback (fiberMap e ArithmeticIndexedFamily.formula) ⋙ (singleRules AxPA e).inference :=
  numeralInferenceComparison AxPA e
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
