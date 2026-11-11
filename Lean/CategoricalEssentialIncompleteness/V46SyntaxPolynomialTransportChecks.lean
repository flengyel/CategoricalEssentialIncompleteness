/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxPolynomialTransport

/-! Both recursive sorts and every coefficient label are compared categorically. -/

@[expose] public section
noncomputable section
universe v₁ v₂ u₁ u₂ w
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
variable {I : Type w} {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable [HasFiniteProducts C] [HasFiniteCoproducts C]
variable [HasFiniteProducts D] [HasFiniteCoproducts D]
variable (E : C ≌ D) (f : I → C) (g : I → D)
variable (χ : ∀ i, E.functor.obj (f i) ≅ g i)

example (p : SyntaxPolynomial I) :
    (p.mapCoefficients f).eval ⋙ E.functor ≅
      (E.prod E).functor ⋙ (p.mapCoefficients g).eval :=
  SyntaxPolynomialTransport.naturalIso E f g χ p

example (p q : SyntaxPolynomial I) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
        (p.mapCoefficients f) (q.mapCoefficients f)) ≌
      Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
        (p.mapCoefficients g) (q.mapCoefficients g)) :=
  SyntaxPolynomialTransport.algebraEquivalence E f g χ p q

example (p q : SyntaxPolynomial I)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (p.mapCoefficients f) (q.mapCoefficients f))) (h : IsInitial A) :
    IsInitial (AlgebraTransport.mappedAlgebra (E.prod E)
      (SyntaxPolynomialTransport.jointIso E f g χ p q) A) :=
  SyntaxPolynomialTransport.initial E f g χ p q A h
