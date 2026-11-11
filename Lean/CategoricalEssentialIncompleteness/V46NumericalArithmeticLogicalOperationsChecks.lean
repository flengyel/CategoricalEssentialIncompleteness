/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticLogicalOperations


/-! # Statement checks in `V46NumericalArithmeticLogicalOperationsChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.LogicalOperations.Checks
open Coordinates SubstitutionParameters
example : numericalSyntax.implicationConstructor ≫ formulaIso.hom =
    (pairedIso formulaIso formulaIso).hom ≫ numericalInterpretation.map originalSyntax.implicationConstructor := implication_square
example : numericalSyntax.equalityConstructor ≫ formulaIso.hom =
    (pairedIso termIso termIso).hom ≫ numericalInterpretation.map originalSyntax.equalityConstructor := equality_square
example : numericalSyntax.quantifierConstructor ≫ formulaIso.hom =
    (pairedIso variableIso formulaIso).hom ≫ numericalInterpretation.map originalSyntax.quantifierConstructor := quantifier_square
example : numericalSyntax.negationConstructor ≫ formulaIso.hom =
    formulaIso.hom ≫ numericalInterpretation.map originalSyntax.negationConstructor := negation_square
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.LogicalOperations.Checks
