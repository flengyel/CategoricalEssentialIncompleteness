import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonStateCoordinates

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.StateCoordinatesChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (U V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
example (formula : Bool) :
    (computedStateFamily T V σ π d U formula).left ≫
      stateResultCodeArrow T (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)) V σ π d formula =
        rawResultArrow T U V σ π d formula :=
  computedState_result T V σ π d U formula
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.StateCoordinatesChecks
