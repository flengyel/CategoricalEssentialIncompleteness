/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonFormulaCommutation


/-! # Statement checks in `V46ConcreteNamedComparisonFormulaCommutationChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.FormulaCommutationChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
example (q : Obj T M
    (((SyntaxPolynomial.formulaExpression V π d).withParameters
      (categoricalSyntax T V σ π d).substitutionParameters).eval.obj
        (projectionSourceAlgebra T V V σ π d).a).left) :
    (F T M).map (categoricalSyntax T V σ π d).substitutionAlgebra.str.2.left
      ((F T M).map (((SyntaxPolynomial.formulaExpression V π d).withParameters
        (categoricalSyntax T V σ π d).substitutionParameters).eval.map
          (computedStatePair T V σ π d)).left q) =
      (F T M).map (computedStatePair T V σ π d).2.left
        ((F T M).map (projectionSourceAlgebra T V V σ π d).str.2.left q) :=
  computedFormula_commutes_model T V σ π d M q
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.FormulaCommutationChecks
