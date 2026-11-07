import CategoricalEssentialIncompleteness.V46NumericalArithmeticSubstitutionParameters
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SubstitutionParameters.Checks
open Coordinates
example : numericalSyntax.substitutionParameters ≅
    numericalInterpretation.obj originalSyntax.substitutionParameters := parameterIso
example : numericalSyntax.algebra.a.2 ⨯ numericalSyntax.substitutionParameters ≅
    numericalInterpretation.obj (originalSyntax.algebra.a.2 ⨯ originalSyntax.substitutionParameters) := formulaInputIso
example : termInputIso.hom ≫ numericalInterpretation.map originalSyntax.termSubstitution =
    numericalSyntax.termSubstitution ≫ termIso.hom := term_substitution
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SubstitutionParameters.Checks
