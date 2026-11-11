/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxOneSort
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxInitial

/-! # Constructed finite-rule tree algebras in the predicate category -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- Ordered rule-labelled trees use precisely the coefficient summands
R₀×1,…,R_N×Xᴺ, without an extra variable summand. -/
def oneSortAlgebra (R : ℕ → PredicateCategory T) (N : ℕ) :
    Endofunctor.Algebra (constructorFunctor R N) :=
  projectedConstructorAlgebra R N
    (postfixAlgebra T (SyntaxPolynomial.constructors R N) .unit)

def oneSortInitial (R : ℕ → PredicateCategory T) (N : ℕ) :
    IsInitial (oneSortAlgebra T R N) :=
  projectedConstructorInitial R N
    (postfixAlgebra T (SyntaxPolynomial.constructors R N) .unit)
    (postfixInitial T (SyntaxPolynomial.constructors R N) .unit)

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
