/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySyntaxAlgebra

/-! # Constructor equations for algebra morphisms from syntax with propositional atoms -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NullarySyntaxAlgebra
variable {D : Type u} [Category.{v} D] [HasFiniteLimits D] [HasFiniteCoproducts D]
variable {E V X : D} {A B : AlgebraWithEmpty E V X} (f : A ⟶ B)

@[reassoc] theorem hom_variable : variableConstructor A ≫ f.f.1 = variableConstructor B := by
  have h := congrArg (fun k => coprod.inl ≫ k) (congrArg Prod.fst f.h)
  simpa [variableConstructor, SyntaxPolynomial.jointFunctor, SyntaxPolynomial.termExpression,
    SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, Category.assoc] using h.symm

@[reassoc] theorem hom_equality : equalityConstructor A ≫ f.f.2 =
    prod.map f.f.1 f.f.1 ≫ equalityConstructor B := by
  have h := congrArg (fun k => (coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl) ≫ k)
    (congrArg Prod.snd f.h)
  simpa [equalityConstructor, SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, Category.assoc] using h.symm

@[reassoc] theorem hom_atom : atomConstructor A ≫ f.f.2 = atomConstructor B := by
  have h := congrArg (fun k => (prod.lift (𝟙 X) (terminal.from X) ≫ coprod.inr ≫
    coprod.inl ≫ coprod.inl ≫ coprod.inl) ≫ k) (congrArg Prod.snd f.h)
  simpa [atomConstructor, SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.constructors, SyntaxPolynomial.power, SyntaxPolynomial.eval,
    SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor, Category.assoc] using h.symm

@[reassoc] theorem hom_negation : negationConstructor A ≫ f.f.2 =
    f.f.2 ≫ negationConstructor B := by
  have h := congrArg (fun k => (coprod.inr ≫ coprod.inl ≫ coprod.inl) ≫ k)
    (congrArg Prod.snd f.h)
  simpa [negationConstructor, SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, Category.assoc] using h.symm

@[reassoc] theorem hom_implication : implicationConstructor A ≫ f.f.2 =
    prod.map f.f.2 f.f.2 ≫ implicationConstructor B := by
  have h := congrArg (fun k => (coprod.inr ≫ coprod.inl) ≫ k) (congrArg Prod.snd f.h)
  simpa [implicationConstructor, SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, Category.assoc] using h.symm

@[reassoc] theorem hom_quantifier : quantifierConstructor A ≫ f.f.2 =
    prod.map (𝟙 V) f.f.2 ≫ quantifierConstructor B := by
  have h := congrArg (fun k => coprod.inr ≫ k) (congrArg Prod.snd f.h)
  simpa [quantifierConstructor, SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
    Category.assoc] using h.symm

end CategoricalEssentialIncompleteness.V46.NullarySyntaxAlgebra
