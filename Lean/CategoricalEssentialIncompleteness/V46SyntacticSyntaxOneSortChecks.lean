/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxOneSort

/-! # Exact finite-rule-polynomial and one-sort universal-property checks -/

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
variable {D : Type u} [Category.{v} D] [HasFiniteProducts D] [HasFiniteCoproducts D]

example (R : ℕ → D) (N : ℕ) (X Y Z : D) (g : Y ⟶ Z) :
    IsIso ((SyntaxPolynomial.constructors R N).eval.map
      ((𝟙 X,g) : (X,Y) ⟶ (X,Z))) := constructors_secondMap_isIso R N X g

example (R : ℕ → D) (N : ℕ)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (SyntaxPolynomial.constructors R N) .unit)) (h : IsInitial A) :
    IsInitial (projectedConstructorAlgebra R N A) := projectedConstructorInitial R N A h
