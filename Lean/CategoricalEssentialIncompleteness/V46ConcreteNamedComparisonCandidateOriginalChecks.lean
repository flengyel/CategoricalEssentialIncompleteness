import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonCandidateOriginal

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.CandidateOriginalChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
example : computedStatePair T V σ π d ≫
    (categoricalSyntax T V σ π d).substitutionOriginalHom.f =
      𝟙 (projectionSourceAlgebra T V V σ π d).a := computedStatePair_original T V σ π d
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.CandidateOriginalChecks
