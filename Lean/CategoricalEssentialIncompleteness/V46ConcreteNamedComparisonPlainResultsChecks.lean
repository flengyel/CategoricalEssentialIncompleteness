/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainResults


/-! # Statement checks in `V46ConcreteNamedComparisonPlainResultsChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.PlainResultsChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (U V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
example : constantFamily (U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T))
      (plainSyntaxCarrier V σ π d true : PredicateCategory T) ⟶
    constantFamily (U ⨯ (plainSyntaxCarrier V σ π d false : PredicateCategory T))
      ((plainSyntaxCarrier V σ π d true : PredicateCategory T) ⨯
        OptionSyntax.obj (plainSyntaxCarrier V σ π d true : PredicateCategory T)) :=
  computedPlainFormulaState T U V σ π d
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.PlainResultsChecks
