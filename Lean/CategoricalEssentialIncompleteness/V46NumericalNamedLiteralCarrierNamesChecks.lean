/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralCarrierNames


/-! # The coded numerical variable object has exactly the named words -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralCarrierNamesChecks
open NumericalNamed
variable (σ π : ℕ → Carrier) (d : ℕ)

example (formula : Bool) (word : ℕ) :
    (SyntacticSyntax.Postfix.plainCarrier formula
      (SyntaxPolynomial.termExpression (NumericalCoordinates.codedPredicate variableObject) σ d)
      (SyntaxPolynomial.formulaExpression (NumericalCoordinates.codedPredicate variableObject) π d)).val.Evalb ![word] ↔
    (SyntacticSyntax.Postfix.plainCarrier formula (NamedPostfixEncoding.termPolynomial σ d)
      (NamedPostfixEncoding.formulaPolynomial π d)).val.Evalb ![word] :=
  coded_plain_native σ π d formula word

end CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralCarrierNamesChecks
