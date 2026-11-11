/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxInitial
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxStableTransport
public import CategoricalEssentialIncompleteness.V46ConcreteDecidableVariables

/-! # Stable named syntax in the actual total split category -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- Transport the constructed postfix algebra for the preimage-labelled
template. Both initiality proofs are transported with the actual algebra,
before normalizing the identity relabelling at the target. -/
def mappedPostfixData {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
    (E : PredicateCategory T ≌ D) (p q : SyntaxPolynomial D) :
    Σ A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q),
      IsInitial A × (∀ R : D, IsInitial (SyntaxPolynomial.algebraWithParameters p q A R)) := by
  let a := p.mapCoefficients E.inverse.obj
  let b := q.mapCoefficients E.inverse.obj
  let A := postfixAlgebra T a b
  have h : Σ B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (p.mapCoefficients id) (q.mapCoefficients id)),
      IsInitial B × (∀ R : D, IsInitial (SyntaxPolynomial.algebraWithParameters
        (p.mapCoefficients id) (q.mapCoefficients id) B R)) :=
    ⟨Transport.mappedAlgebra E E.inverse.obj id (fun X => E.counitIso.app X) p q A,
      SyntaxPolynomialTransport.initial E E.inverse.obj id
        (fun X => E.counitIso.app X) p q A (postfixInitial T a b),
      Transport.mappedStable E E.inverse.obj id (fun X => E.counitIso.app X)
        p q A (fun R => withParametersInitial T R a b)⟩
  let S := fun r s : SyntaxPolynomial D =>
    Σ B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor r s),
      IsInitial B × (∀ R : D, IsInitial (SyntaxPolynomial.algebraWithParameters r s B R))
  exact Eq.mp (congrArg₂ S (mapCoefficients_id p) (mapCoefficients_id q)) h

/-- Every total split object may serve as variables or as any finite
arity coefficient. No total evaluator is part of the input data. -/
def totalCategoricalSyntax (V : TotalSplit T) (σ π : ℕ → TotalSplit T) (d : ℕ) :
    CategoricalSyntax V σ π d where
  decidableVariables := ConcreteDecidableVariables.total T V
  algebra := (mappedPostfixData T (predicateEquivalence T)
    (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).1
  initial := (mappedPostfixData T (predicateEquivalence T)
    (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).2.1
  stable := (mappedPostfixData T (predicateEquivalence T)
    (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).2.2
  lists := SyntacticLists.totalStableListAlgebra T V

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
