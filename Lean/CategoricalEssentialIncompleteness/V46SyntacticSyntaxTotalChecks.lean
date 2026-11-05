/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxTotal

/-! # Explicit categorical signature checks for Total -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example (V : TotalSplit T) (σ π : ℕ → TotalSplit T) (d : ℕ) :
    CategoricalSyntax V σ π d := totalCategoricalSyntax T V σ π d

example (V : TotalSplit T) (σ π : ℕ → TotalSplit T) (d : ℕ) (P : TotalSplit T) :
    IsInitial (SyntaxPolynomial.algebraWithParameters
      (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
        (totalCategoricalSyntax T V σ π d).algebra P) :=
  (totalCategoricalSyntax T V σ π d).stable P
