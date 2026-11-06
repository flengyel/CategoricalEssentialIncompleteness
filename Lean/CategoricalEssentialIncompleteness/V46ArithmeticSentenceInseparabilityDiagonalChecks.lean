import CategoricalEssentialIncompleteness.V46ArithmeticSentenceInseparabilityDiagonal
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticSentenceInseparabilityDiagonalChecks
example :
    ¬ ∃ C : Set ℕ, ComputablePred (· ∈ C) ∧
      {n : ℕ | ArithmeticDiagonalCodes.alpha.val.Evalb ![n]} ⊆ C ∧
      Disjoint C {n : ℕ | ArithmeticDiagonalCodes.beta.val.Evalb ![n]} :=
  ArithmeticSentenceInseparability.diagonal_no_recursive_separator
end CategoricalEssentialIncompleteness.V46.ArithmeticSentenceInseparabilityDiagonalChecks
