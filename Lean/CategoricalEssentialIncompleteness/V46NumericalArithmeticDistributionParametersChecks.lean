import CategoricalEssentialIncompleteness.V46NumericalArithmeticDistributionParameters
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.DistributionParameters.Checks
open Coordinates RuleParameters
example : numericalSyntax.distributionParameters ≅ numericalInterpretation.obj originalSyntax.distributionParameters := iso
example : iso.hom ≫ numericalInterpretation.map originalSyntax.distributionInclusion =
    numericalSyntax.distributionInclusion ≫ distributionBaseIso.hom := inclusion
example (q : NumericalTuples.Point
    (NumericalNamed.variableObject ⨯ (numericalSyntax.algebra.a.2 ⨯ numericalSyntax.algebra.a.2))) :
    (∃ a, numericalSyntax.distributionInclusion.toFun a = q) ↔
      ∃ a : NumericalTuples.Point (numericalInterpretation.obj originalSyntax.distributionParameters),
        (numericalInterpretation.map originalSyntax.distributionInclusion).toFun a =
          distributionBaseIso.hom.toFun q := image_iff q
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.DistributionParameters.Checks
