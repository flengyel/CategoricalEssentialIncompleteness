/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DerivationStandardInductionCharts


/-! # Constructor charts for the constructed derivation trees -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.DerivationStandardInductionChartsChecks
open SyntacticSyntax SyntacticDerivation SyntacticDerivation.StandardInduction
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
example (labels : ℕ → PredicateCategory T) (N : ℕ) :
    projectedInput T labels N ≫ (oneSortAlgebra T labels N).str =
      (postfixAlgebra T (SyntaxPolynomial.constructors labels N) .unit).str.1 :=
  projectedInput_structure T labels N
example {F₀ : PredicateCategory T} {N : ℕ} (R : RulePresentation F₀ N) :
    ordinaryInput T R ≫ (ordinaryTree T R).str =
      (postfixAlgebra T (SyntaxPolynomial.constructors (PolynomialComparison.coefficients R) N) .unit).str.1 :=
  ordinaryInput_structure T R
end CategoricalEssentialIncompleteness.V46.DerivationStandardInductionChartsChecks
