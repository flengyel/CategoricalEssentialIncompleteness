/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTracePrimitiveHistory


/-! # Primitive recursiveness of the history evaluator -/

@[expose] public section
open Nat Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator
open CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveCoding

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveHistoryChecks
example : ∃ f : List.Vector ℕ 3 → ℕ, Computes codeHistoryEvaluator f ∧ Primrec f :=
  PrimitiveTotal.historyEvaluator

example : PrimitiveTotal codeEvaluatorHistory := PrimitiveTotal.evaluatorHistory
end CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveHistoryChecks
