/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticSubstitutionDomains


/-! # Statement checks in `V46NumericalArithmeticSubstitutionDomainsChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SubstitutionDomains.Checks
open Coordinates SubstitutionParameters
example : numericalSyntax.admissibleSubstitution ≅
    numericalInterpretation.obj originalSyntax.admissibleSubstitution := admissibleIso
example : admissibleIso.hom ≫ numericalInterpretation.map originalSyntax.admissibleInclusion =
    numericalSyntax.admissibleInclusion ≫ formulaInputIso.hom := forward_inclusion
example : admissibleIso.inv ≫ numericalSyntax.admissibleInclusion =
    numericalInterpretation.map originalSyntax.admissibleInclusion ≫ formulaInputIso.inv := backward_inclusion
example : admissibleIso.hom ≫ numericalInterpretation.map originalSyntax.formulaSubstitution =
    numericalSyntax.formulaSubstitution ≫ formulaIso.hom := admissible_result
example (q : NumericalTuples.Point (numericalSyntax.algebra.a.2 ⨯ numericalSyntax.substitutionParameters)) :
    (∃ a, numericalSyntax.admissibleInclusion.toFun a = q) ↔
      ∃ a : NumericalTuples.Point (numericalInterpretation.obj originalSyntax.admissibleSubstitution),
        (numericalInterpretation.map originalSyntax.admissibleInclusion).toFun a = formulaInputIso.hom.toFun q :=
  admissible_image_iff q
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SubstitutionDomains.Checks
