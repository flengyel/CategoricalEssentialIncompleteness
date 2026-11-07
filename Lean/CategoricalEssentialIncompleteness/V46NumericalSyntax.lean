/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalStableLists
import CategoricalEssentialIncompleteness.V46ConcreteDecidableVariables
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlainTotal
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxOneSortTotal

/-! # Parameter-stable syntax in the numerical tuple category -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalSyntax

/-- The full standard theory presents all numerical carrier-total morphisms. -/
def predicateEquivalence : PredicateCategory 𝗧𝗔 ≌ NumericalTuples.Object :=
  (SyntacticPredicates.predicateEquivalence 𝗧𝗔).trans NumericalStableLists.numericalEquivalence

/-- The literal postfix algebra is transported with its parameterized initiality. -/
def data (p q : SyntaxPolynomial NumericalTuples.Object) :
    Σ A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q),
      IsInitial A × (∀ P : NumericalTuples.Object,
        IsInitial (SyntaxPolynomial.algebraWithParameters p q A P)) :=
  SyntacticSyntax.mappedPlainPostfixData 𝗧𝗔 predicateEquivalence p q

/-- Arbitrary numerical coefficients are allowed, including empty carriers and arity zero. -/
def categoricalSyntax (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ) :
    CategoricalSyntax V σ π d where
  decidableVariables := ConcreteDecidableVariables.numerical V
  algebra := (data (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)).1
  initial := (data (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)).2.1
  stable := (data (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)).2.2
  lists := NumericalStableLists.stableListAlgebra V

/-- Numerical finite-rule trees use the same ordered constructor polynomial. -/
def oneSortAlgebra (R : ℕ → NumericalTuples.Object) (N : ℕ) :
    Endofunctor.Algebra (SyntacticSyntax.constructorFunctor R N) :=
  SyntacticSyntax.projectedConstructorAlgebra R N
    (data (SyntaxPolynomial.constructors R N) .unit).1

def oneSortInitial (R : ℕ → NumericalTuples.Object) (N : ℕ) :
    IsInitial (oneSortAlgebra R N) :=
  SyntacticSyntax.projectedConstructorInitial R N
    (data (SyntaxPolynomial.constructors R N) .unit).1
    (data (SyntaxPolynomial.constructors R N) .unit).2.1

end CategoricalEssentialIncompleteness.V46.NumericalSyntax
