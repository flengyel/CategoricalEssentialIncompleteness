import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralAlgorithms

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralAlgorithmsChecks
open NumericalNamed
variable (V W : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (word : M) : ConcreteNamedSubstitution.freeVariables V σ π d word =
    ConcreteNamedSubstitution.freeVariables W σ π d word :=
  freeVariables_variable_parameter V W σ π d word
example (x replacement word : M) : ConcreteNamedSubstitution.substitutionResult V σ π d x replacement word =
    ConcreteNamedSubstitution.substitutionResult W σ π d x replacement word :=
  substitutionResult_variable_parameter V W σ π d x replacement word
example (x replacement word : M) : ConcreteNamedSubstitution.substitutionFreeFor V σ π d x replacement word =
    ConcreteNamedSubstitution.substitutionFreeFor W σ π d x replacement word :=
  substitutionFreeFor_variable_parameter V W σ π d x replacement word

end CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralAlgorithmsChecks
