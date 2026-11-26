module

import CategoricalEssentialIncompleteness.V46NumericalSyntaxMembership
import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralPresentation

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46

namespace V81Reconciliation

/-- The first reader's two supports in the literal algebra are the second reader's
unary supports, for every bound and every family of unary coefficients. -/
theorem literal_supports (d : ℕ) (σ π : ℕ → EnumerableCarriers.Total) :
    let V := NumericalNamed.variableObject
    let s := fun k => NumericalTuples.unary (σ k)
    let p := fun k => NumericalTuples.unary (π k)
    let A := NumericalNamed.literalWordAlgebra V s p d
    let terms := SyntaxPolynomial.termExpression (NumericalCoordinates.codedPredicate V)
      (fun k => NumericalCoordinates.codedPredicate (s k)) d
    let formulas := SyntaxPolynomial.formulaExpression (NumericalCoordinates.codedPredicate V)
      (fun k => NumericalCoordinates.codedPredicate (p k)) d
    let W := fun b => NumericalCoordinates.predicateObject
      (SyntacticSyntax.Postfix.plainCarrier b terms formulas)
    A.a.1.support = (W false).support ∧ A.a.2.support = (W true).support :=
  ⟨rfl, rfl⟩

#print axioms literal_supports

end V81Reconciliation
