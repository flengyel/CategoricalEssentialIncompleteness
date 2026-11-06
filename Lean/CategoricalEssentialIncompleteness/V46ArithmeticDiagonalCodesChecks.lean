import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodes

/-! # Exact statement checks for the arithmetic diagonal construction -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.ProofSearch FailureOfComposition.TypedTuringMorphism

namespace CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalCodes.Checks
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example : 𝗣𝗔 ⊢ diagonalComparisonSentence := diagonal_comparison_PA
example : 𝗣𝗔 ⊢ diagonalSourceSentence := diagonal_source_PA
example : 𝗣𝗔 ⊢ disjointSentence := disjoint_PA
example (x y : M) :
    UniformTrace.graph.val.Evalb ![(diagonalIndex : M),x,y] ↔
      UniformTrace.graph.val.Evalb ![x,x,y] := diagonal_graph x y
example (x : M) : ¬(alpha.val.Evalb ![x] ∧ beta.val.Evalb ![x]) := output_disjoint x
example (n : ℕ) (h : alpha.val.Evalb (M := ℕ) ![n]) :
    𝗣𝗔 ⊢ (alpha.val/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) :=
  output_numeral_PA 0 n h
example (n : ℕ) (h : beta.val.Evalb (M := ℕ) ![n]) :
    𝗣𝗔 ⊢ ∼(alpha.val/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) :=
  beta_numeral_refutes_alpha n h
end CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalCodes.Checks
