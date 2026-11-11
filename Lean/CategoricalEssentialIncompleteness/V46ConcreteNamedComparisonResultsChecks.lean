/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonResults


/-! # Statement checks in `V46ConcreteNamedComparisonResultsChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.ResultsChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (U V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
example (formula : Bool) : GraphMorphism T (payloadInputCarrier U V σ π d formula)
    (rawResultCarrier V σ π d formula) := resultMorphism T U V σ π d formula
example : constantFamily (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T))
      (syntaxCarrier V σ π d true : PredicateCategory T) ⟶
    constantFamily (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T))
      ((syntaxCarrier V σ π d true : PredicateCategory T) ⨯
        OptionSyntax.obj (syntaxCarrier V σ π d true : PredicateCategory T)) :=
  computedFormulaState T U V σ π d
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.ResultsChecks
