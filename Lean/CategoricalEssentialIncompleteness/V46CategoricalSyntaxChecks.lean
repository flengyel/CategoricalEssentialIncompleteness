/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSyntax

/-! Explicit polynomial types and folds into arbitrary parameter families. -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [HasFiniteLimits D] [HasFiniteCoproducts D]

example (V X Y : D) (σ : ℕ → D) (d : ℕ) :
    (SyntaxPolynomial.termExpression V σ d).eval.obj (X, Y) =
      (V ⨿ (SyntaxPolynomial.constructors σ d).eval.obj (X, Y)) := rfl

example (V X Y : D) (π : ℕ → D) (d : ℕ) :
    (SyntaxPolynomial.formulaExpression V π d).eval.obj (X, Y) =
      (((((X ⨯ X) ⨿ (SyntaxPolynomial.constructors π d).eval.obj (X, Y)) ⨿ Y) ⨿
        (Y ⨯ Y)) ⨿ (V ⨯ Y)) := rfl

example (p q : SyntaxPolynomial D) {X Y : D × D} (f : X ⟶ Y) :
    (SyntaxPolynomial.product p q).eval.map f = prod.map (p.eval.map f) (q.eval.map f) := rfl

example (p q : SyntaxPolynomial D) {X Y : D × D} (f : X ⟶ Y) :
    (SyntaxPolynomial.sum p q).eval.map f = coprod.map (p.eval.map f) (q.eval.map f) := rfl

example {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    (SyntaxPolynomial.term : SyntaxPolynomial D).eval.map ((f, g) : (X, Y) ⟶ (X', Y')) = f := rfl

example {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    (SyntaxPolynomial.formula : SyntaxPolynomial D).eval.map ((f, g) : (X, Y) ⟶ (X', Y')) = g := rfl

example (X Y : D) : (SyntaxPolynomial.power (.term : SyntaxPolynomial D) 0).eval.obj
    (X, Y) = ⊤_ D := rfl

example (X Y : D) : (SyntaxPolynomial.power (.term : SyntaxPolynomial D) 1).eval.obj
    (X, Y) = X := rfl

example (X Y : D) : (SyntaxPolynomial.power (.term : SyntaxPolynomial D) 2).eval.obj
    (X, Y) = (X ⨯ X) := rfl

example {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d) (P : D)
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      ((SyntaxPolynomial.termExpression V σ d).withParameters P)
      ((SyntaxPolynomial.formulaExpression V π d).withParameters P))) :
    (constantFamily P S.algebra.a.1, constantFamily P S.algebra.a.2) ⟶ B.a :=
  S.foldWithParameters P B
