/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticRuleParameters


/-! # The arithmetic scheme-parameter product and success comparisons -/

@[expose] public section
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
