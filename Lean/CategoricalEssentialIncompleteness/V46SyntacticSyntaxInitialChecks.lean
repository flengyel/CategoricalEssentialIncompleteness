/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxInitial

/-! # Explicit categorical signature checks for Initial -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example (P : PredicateCategory T) (a b : SyntaxPolynomial (PredicateCategory T)) :
    IsInitial (SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P) :=
  withParametersInitial T P a b

example (a b : SyntaxPolynomial (PredicateCategory T)) : IsInitial (postfixAlgebra T a b) :=
  postfixInitial T a b

example (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ) :
    CategoricalSyntax V σ π d := categoricalSyntax T V σ π d
