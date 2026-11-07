import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralEquivalence

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralEquivalenceChecks
open NumericalNamed

example : literalEquivalence.functor = NumericalSyntax.predicateEquivalence.functor :=
  literalEquivalence_functor
example (C : NumericalTuples.Object) :
    literalEquivalence.inverse.obj C = NumericalCoordinates.codedPredicate C :=
  literalEquivalence_inverse_obj C
example (C : NumericalTuples.Object) :
    literalEquivalence.counitIso.app C = NumericalCoordinates.coefficientIso C :=
  literalEquivalence_counit C

end CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralEquivalenceChecks
