import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainSubstitutionComparison

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.PlainSubstitutionComparisonChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

example : (categoricalSyntax T V σ π d).termSubstitution ≫
    (syntaxPlainIso T V σ π d false).hom =
    (plainPublicInputIso T V σ π d false).hom ≫
      (plainCategoricalSyntax T V σ π d).termSubstitution :=
  plain_termSubstitution_comparison T V σ π d

example : (categoricalSyntax T V σ π d).formulaSubstitutionOption ≫
    OptionSyntax.map (syntaxPlainIso T V σ π d true).hom =
    (plainPublicInputIso T V σ π d true).hom ≫
      (plainCategoricalSyntax T V σ π d).formulaSubstitutionOption :=
  plain_formulaSubstitutionOption_comparison T V σ π d
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.PlainSubstitutionComparisonChecks
