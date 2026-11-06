import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonProjectionLaws

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.ProjectionLawsChecks
variable (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example (x t u : M)
    (hu : (rawCarrier (syntaxCarrier V σ π d false) (syntaxCarrier V σ π d true)
      (SyntaxPolynomial.termExpression V σ d)).val.Evalb ![u]) :
    originalComputation V σ π d x t (Coding.constructor false (SyntaxPolynomial.termExpression V σ d) u) =
      Coding.constructor false (SyntaxPolynomial.termExpression V σ d)
        (ConcreteNamedSubstitution.mapChildren (originalComputation V σ π d x t)
          (originalComputation V σ π d x t) (SyntaxPolynomial.termExpression V σ d) u) :=
  originalComputation_term_constructor V σ π d x t u hu
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.ProjectionLawsChecks
