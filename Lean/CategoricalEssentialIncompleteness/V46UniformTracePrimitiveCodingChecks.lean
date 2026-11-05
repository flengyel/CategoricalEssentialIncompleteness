import CategoricalEssentialIncompleteness.V46UniformTracePrimitiveCoding

/-! # Checks for the uniform trace construction -/

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveCodingChecks

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.UniformTrace

example : PrimitiveCoding.PrimitiveTotal traceProgram :=
  PrimitiveCoding.PrimitiveTotal.traceProgram

example : PrimrecPred (fun p : ℕ × ℕ × ℕ =>
    traceFormula.val.Evalb ![p.1, p.2.1, p.2.2]) := trace_primrec

example : Nat.Primrec (fun n : ℕ =>
    traceCheck n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2) := traceCheck_natPrimrec

example : Nat.Primrec (out : ℕ → ℕ) := out_natPrimrec

example : 𝗣𝗔 ⊢ traceComparisonSentence := trace_comparison_PA

example : 𝗣𝗔 ⊢ primitiveTraceGraphSentence := primitive_trace_graph_PA

end CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveCodingChecks
