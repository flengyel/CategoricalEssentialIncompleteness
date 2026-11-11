/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralVariables


/-! # Statement checks in `V46NumericalNamedLiteralVariablesChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralVariablesChecks
open NumericalNamed

example : variableObject.dimension = 1 := rfl
example (n : ℕ) : (NumericalCoordinates.codedPredicate variableObject).val.Evalb ![n] :=
  codedVariable_member n
example (C : NumericalTuples.Object) (x : NumericalTuples.Point C) :
    ((NumericalCoordinates.predicatePresentationIso (NumericalCoordinates.codedPredicate C)).hom.toFun
      ((NumericalCoordinates.coefficientIso C).inv.toFun x)).val =
        NumericalTuples.code C.dimension x.val := coefficient_inverse_code x
example (n : ℕ) :
    ((NumericalCoordinates.predicatePresentationIso (NumericalCoordinates.codedPredicate variableObject)).hom.toFun
      ((literalEquivalence.counitIso.app variableObject).inv.toFun (variablePoint n))).val = n :=
  variable_name_code n

end CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralVariablesChecks
