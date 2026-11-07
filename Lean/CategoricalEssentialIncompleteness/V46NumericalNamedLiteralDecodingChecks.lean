import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralDecoding

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralDecodingChecks
open NumericalNamed
variable (σ π : ℕ → NumericalTuples.Object) (d : ℕ)

example (x : NumericalTuples.Point (literalCategoricalSyntax variableObject σ π d).algebra.a.1) :
    ∃ r : NamedFiniteSyntax.Term
        (NamedPostfixEncoding.Symbols (fun n => NumericalCoordinates.codedPredicate (σ n))) d,
      NamedPostfixEncoding.termCode r =
        ((literalTermPresentationIso variableObject σ π d).hom.toFun x).val := literal_term_decodes σ π d x
example (x : NumericalTuples.Point (literalCategoricalSyntax variableObject σ π d).algebra.a.2) :
    ∃ φ : NamedFiniteSyntax.Formula
        (NamedPostfixEncoding.Symbols (fun n => NumericalCoordinates.codedPredicate (σ n)))
        (NamedPostfixEncoding.Symbols (fun n => NumericalCoordinates.codedPredicate (π n))) d,
      NamedPostfixEncoding.formulaCode φ =
        ((literalFormulaPresentationIso variableObject σ π d).hom.toFun x).val := literal_formula_decodes σ π d x

end CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralDecodingChecks
