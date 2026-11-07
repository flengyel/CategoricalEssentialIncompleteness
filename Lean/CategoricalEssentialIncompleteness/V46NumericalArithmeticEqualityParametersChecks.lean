import CategoricalEssentialIncompleteness.V46NumericalArithmeticEqualityParameters
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.EqualityParameters.Checks
open Coordinates SubstitutionDomains RuleParameters
example : numericalSyntax.equalitySchemeParameters ≅
    numericalInterpretation.obj originalSyntax.equalitySchemeParameters := equalityIso
example : equalityIso.hom ≫ numericalInterpretation.map originalSyntax.equalitySchemeInclusion =
    numericalSyntax.equalitySchemeInclusion ≫ equalityBaseIso.hom := equality_inclusion
example : equalityIso.hom ≫ numericalInterpretation.map originalSyntax.equalityFirstAdmissible =
    numericalSyntax.equalityFirstAdmissible ≫ admissibleIso.hom := equality_first_admissible
example : equalityIso.hom ≫ numericalInterpretation.map originalSyntax.equalitySecondAdmissible =
    numericalSyntax.equalitySecondAdmissible ≫ admissibleIso.hom := equality_second_admissible
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.EqualityParameters.Checks
