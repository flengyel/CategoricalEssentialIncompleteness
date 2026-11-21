/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticSentenceInseparabilityDiagonal


/-! # The categorical obstruction to a recursive diagonal separator -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticSentenceInseparabilityDiagonalChecks
example :
    ¬ ∃ C : Set ℕ, ComputablePred (· ∈ C) ∧
      {n : ℕ | ArithmeticDiagonalCodes.alpha.val.Evalb ![n]} ⊆ C ∧
      Disjoint C {n : ℕ | ArithmeticDiagonalCodes.beta.val.Evalb ![n]} :=
  ArithmeticSentenceInseparability.diagonal_no_recursive_separator
end CategoricalEssentialIncompleteness.V46.ArithmeticSentenceInseparabilityDiagonalChecks
