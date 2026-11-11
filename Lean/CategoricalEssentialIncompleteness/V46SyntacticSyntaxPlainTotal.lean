/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlain
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxTotal

/-! # The plain postfix syntax bundle in the actual total split category -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

def mappedPlainPostfixData {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
    (E : PredicateCategory T ≌ D) (p q : SyntaxPolynomial D) :
    Σ A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q),
      IsInitial A × (∀ R : D, IsInitial (SyntaxPolynomial.algebraWithParameters p q A R)) := by
  let a := p.mapCoefficients E.inverse.obj
  let b := q.mapCoefficients E.inverse.obj
  let A := plainPostfixAlgebra T a b
  have h : Σ B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (p.mapCoefficients id) (q.mapCoefficients id)),
      IsInitial B × (∀ R : D, IsInitial (SyntaxPolynomial.algebraWithParameters
        (p.mapCoefficients id) (q.mapCoefficients id) B R)) :=
    ⟨Transport.mappedAlgebra E E.inverse.obj id (fun X => E.counitIso.app X) p q A,
      SyntaxPolynomialTransport.initial E E.inverse.obj id
        (fun X => E.counitIso.app X) p q A (plainPostfixInitial T a b),
      Transport.mappedStable E E.inverse.obj id (fun X => E.counitIso.app X)
        p q A (fun R => plainWithParametersInitial T a b R)⟩
  let S := fun r s : SyntaxPolynomial D =>
    Σ B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor r s),
      IsInitial B × (∀ R : D, IsInitial (SyntaxPolynomial.algebraWithParameters r s B R))
  exact Eq.mp (congrArg₂ S (mapCoefficients_id p) (mapCoefficients_id q)) h

/-- The plain parser carriers and constructors give the required
initial syntax algebra in every actual total-split parameter slice. -/
def plainTotalCategoricalSyntax (V : TotalSplit T) (σ π : ℕ → TotalSplit T) (d : ℕ) :
    CategoricalSyntax V σ π d where
  decidableVariables := ConcreteDecidableVariables.total T V
  algebra := (mappedPlainPostfixData T (predicateEquivalence T)
    (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).1
  initial := (mappedPlainPostfixData T (predicateEquivalence T)
    (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).2.1
  stable := (mappedPlainPostfixData T (predicateEquivalence T)
    (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).2.2
  lists := SyntacticLists.totalStableListAlgebra T V

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
