import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralNegation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralNegationChecks
open NumericalNamed
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)

example : literalEquivalence.functor.map (literalSourceSyntax V σ π d).sentenceNegation ≫
      (literalSentenceIso V σ π d).hom =
    (literalSentenceIso V σ π d).hom ≫ (literalCategoricalSyntax V σ π d).sentenceNegation :=
  literal_sentenceNegation_comparison V σ π d

example : (literalCategoricalSyntax V σ π d).sentenceNegation ≫
      (literalSentencePresentationIso V σ π d).hom =
    (literalSentencePresentationIso V σ π d).hom ≫
      NumericalCoordinates.predicateMap (literalSourceSyntax V σ π d).sentenceNegation :=
  literal_sentenceNegation_code_square V σ π d

example (s : NumericalTuples.Point (literalCategoricalSyntax V σ π d).sentenceObject) :
    literalSentenceWord V σ π d ((literalCategoricalSyntax V σ π d).sentenceNegation.toFun s) =
    SyntacticSyntax.Coding.constructor (M := ℕ) true
      (SyntaxPolynomial.formulaExpression (NumericalCoordinates.codedPredicate V)
        (fun n => NumericalCoordinates.codedPredicate (π n)) d)
      (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (literalSentenceWord V σ π d s) 1) 0) 0) :=
  literal_sentenceNegation_value V σ π d s

example (s : NumericalTuples.Point (literalCategoricalSyntax variableObject σ π d).sentenceObject) :
    ∃ φ : NamedFiniteSyntax.Formula
        (NamedPostfixEncoding.Symbols (fun n => NumericalCoordinates.codedPredicate (σ n)))
        (NamedPostfixEncoding.Symbols (fun n => NumericalCoordinates.codedPredicate (π n))) d,
      φ.freeVariables = [] ∧ literalSentenceWord variableObject σ π d s = NamedPostfixEncoding.formulaCode φ ∧
        literalSentenceWord variableObject σ π d
          ((literalCategoricalSyntax variableObject σ π d).sentenceNegation.toFun s) =
            NamedPostfixEncoding.formulaCode (.neg φ) :=
  literal_sentenceNegation_formulaCode σ π d s

end CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralNegationChecks
