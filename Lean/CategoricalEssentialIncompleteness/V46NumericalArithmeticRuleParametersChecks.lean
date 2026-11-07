import CategoricalEssentialIncompleteness.V46NumericalArithmeticRuleParameters
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.RuleParameters.Checks
open Coordinates SubstitutionParameters SubstitutionDomains
example : numericalSyntax.instantiationParameters ≅
    numericalInterpretation.obj originalSyntax.instantiationParameters := instantiationIso
example : instantiationIso.hom ≫ numericalInterpretation.map originalSyntax.instantiationInclusion =
    numericalSyntax.instantiationInclusion ≫ instantiationBaseIso.hom := instantiation_inclusion
example : instantiationIso.hom ≫ numericalInterpretation.map originalSyntax.instantiationAdmissible =
    numericalSyntax.instantiationAdmissible ≫ admissibleIso.hom := instantiation_admissible
example : numericalSyntax.equalitySchemeBase ≅
    numericalInterpretation.obj originalSyntax.equalitySchemeBase := equalityBaseIso
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.RuleParameters.Checks
