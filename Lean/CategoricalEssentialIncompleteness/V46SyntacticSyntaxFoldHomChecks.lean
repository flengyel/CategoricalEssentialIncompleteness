/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxFoldHom

/-! # Explicit categorical signature checks for FoldHom -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example (P : PredicateCategory T) (a b : SyntaxPolynomial (PredicateCategory T))
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (a.withParameters P) (b.withParameters P))) :
    SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P ⟶ B :=
  foldHom T a b B
