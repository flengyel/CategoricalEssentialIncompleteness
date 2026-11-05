import CategoricalEssentialIncompleteness.V46UniformTracePrimitiveHistory

open Nat Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator
open CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveCoding

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveHistoryChecks
example : ∃ f : List.Vector ℕ 3 → ℕ, Computes codeHistoryEvaluator f ∧ Primrec f :=
  PrimitiveTotal.historyEvaluator

example : PrimitiveTotal codeEvaluatorHistory := PrimitiveTotal.evaluatorHistory
end CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveHistoryChecks
