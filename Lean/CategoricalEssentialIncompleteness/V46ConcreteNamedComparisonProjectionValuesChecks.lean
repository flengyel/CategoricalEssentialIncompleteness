import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonProjectionValues

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.ProjectionValuesChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (U V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example (formula : Bool) (x t word : M) (hx : U.val.Evalb ![x])
    (ht : (syntaxCarrier V σ π d false).val.Evalb ![t])
    (hw : (syntaxCarrier V σ π d formula).val.Evalb ![word]) :
    originalComputation V σ π d x t word = word :=
  originalComputation_identity T U V σ π d M formula x t word hx ht hw
example (formula : Bool) (x t word : M) (hx : U.val.Evalb ![x])
    (ht : (syntaxCarrier V σ π d false).val.Evalb ![t])
    (hw : (syntaxCarrier V σ π d formula).val.Evalb ![word]) :
    occurrenceComputation V σ π d x t word = ConcreteNamedSubstitution.freeVariables V σ π d word :=
  occurrenceComputation_identity T U V σ π d M formula x t word hx ht hw
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.ProjectionValuesChecks
