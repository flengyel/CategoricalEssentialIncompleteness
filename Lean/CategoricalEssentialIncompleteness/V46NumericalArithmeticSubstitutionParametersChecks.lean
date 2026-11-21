/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticSubstitutionParameters


/-! # Arithmetic substitution parameter and input comparisons -/

@[expose] public section
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
