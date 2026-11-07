import CategoricalEssentialIncompleteness.V46NumericalArithmeticCoordinates
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Coordinates.Checks
example : numericalSyntax.algebra.a.2 ≅ numericalInterpretation.obj originalSyntax.algebra.a.2 := formulaIso
example : numericalSyntax.algebra.a.1 ≅ numericalInterpretation.obj originalSyntax.algebra.a.1 := termIso
example : numericalSyntax.sentenceObject ≅ numericalInterpretation.obj originalSyntax.sentenceObject := sentenceIso
example : sentenceIso.hom ≫ numericalInterpretation.map originalSyntax.sentenceInclusion =
    numericalSyntax.sentenceInclusion ≫ formulaIso.hom := sentence_inclusion
example :
    let e : numericalSyntax.algebra.a.2 ≅ numericalInterpretation.obj originalSyntax.algebra.a.2 := formulaIso
    let w : numericalSyntax.algebra.a.2 ≅ NumericalCoordinates.predicateObject sourceSyntax.algebra.a.2 :=
      NumericalNamed.literalFormulaPresentationIso NumericalNamed.variableObject functions relations NamedArithmeticSignature.bound
    ∀ φ : NumericalTuples.Point numericalSyntax.algebra.a.2,
      NumericalTuples.code (numericalInterpretation.obj originalSyntax.algebra.a.2).dimension
          (e.hom.toFun φ).val =
        NumericalTuples.code (NumericalCoordinates.predicateObject sourceSyntax.algebra.a.2).dimension
          (w.hom.toFun φ).val := by
  dsimp only
  intro φ
  exact congrArg (NumericalTuples.code 1) (formulaIso_value φ)
example :
    let e : numericalSyntax.algebra.a.2 ≅ numericalInterpretation.obj originalSyntax.algebra.a.2 := formulaIso
    let w : numericalSyntax.algebra.a.2 ≅ NumericalCoordinates.predicateObject sourceSyntax.algebra.a.2 :=
      NumericalNamed.literalFormulaPresentationIso NumericalNamed.variableObject functions relations NamedArithmeticSignature.bound
    ∀ φ : NumericalTuples.Point (numericalInterpretation.obj originalSyntax.algebra.a.2),
      NumericalTuples.code (NumericalCoordinates.predicateObject sourceSyntax.algebra.a.2).dimension
          (w.hom.toFun (e.inv.toFun φ)).val =
        NumericalTuples.code (numericalInterpretation.obj originalSyntax.algebra.a.2).dimension φ.val := by
  dsimp only
  intro φ
  exact congrArg (NumericalTuples.code 1) (formulaIso_inverse_value φ)
example : (numericalInterpretation.obj originalSyntax.algebra.a.2).dimension = 1 := rfl
example : (NumericalCoordinates.predicateObject sourceSyntax.algebra.a.2).dimension = 1 := rfl
example (n : ℕ) : NumericalTuples.code 1 n = n := NumericalTuples.code_one n
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Coordinates.Checks
