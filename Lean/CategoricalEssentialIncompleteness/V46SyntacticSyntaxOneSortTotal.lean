/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxOneSortInitial
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxTotal

/-! # Initial finite-rule tree algebras in the actual total split category -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

def totalOneSortAlgebra (R : ℕ → TotalSplit T) (N : ℕ) :
    Endofunctor.Algebra (constructorFunctor R N) :=
  projectedConstructorAlgebra R N
    (mappedPostfixData T (predicateEquivalence T)
      (SyntaxPolynomial.constructors R N) .unit).1

def totalOneSortInitial (R : ℕ → TotalSplit T) (N : ℕ) :
    IsInitial (totalOneSortAlgebra T R N) :=
  projectedConstructorInitial R N
    (mappedPostfixData T (predicateEquivalence T)
      (SyntaxPolynomial.constructors R N) .unit).1
    (mappedPostfixData T (predicateEquivalence T)
      (SyntaxPolynomial.constructors R N) .unit).2.1

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
