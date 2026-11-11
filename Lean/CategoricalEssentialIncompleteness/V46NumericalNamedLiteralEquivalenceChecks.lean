/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralEquivalence


/-! # Statement checks in `V46NumericalNamedLiteralEquivalenceChecks` -/

@[expose] public section
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
