/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticSchemeSquares


/-! # Arithmetic diagrams for the Hilbert axiom schemes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SchemeSquares.Checks
open Coordinates SubstitutionParameters RuleParameters EqualityParameters
example : formulaPairIso.hom ≫ numericalInterpretation.map originalSyntax.hilbertOne =
    numericalSyntax.hilbertOne ≫ formulaIso.hom := hilbertOne
example : formulaTripleIso.hom ≫ numericalInterpretation.map originalSyntax.hilbertTwo =
    numericalSyntax.hilbertTwo ≫ formulaIso.hom := hilbertTwo
example : formulaPairIso.hom ≫ numericalInterpretation.map originalSyntax.hilbertThree =
    numericalSyntax.hilbertThree ≫ formulaIso.hom := hilbertThree
example : instantiationIso.hom ≫ numericalInterpretation.map originalSyntax.hilbertInstantiation =
    numericalSyntax.hilbertInstantiation ≫ formulaIso.hom := hilbertInstantiation
example : DistributionParameters.iso.hom ≫ numericalInterpretation.map originalSyntax.hilbertDistribution =
    numericalSyntax.hilbertDistribution ≫ formulaIso.hom := hilbertDistribution
example : termIso.hom ≫ numericalInterpretation.map originalSyntax.hilbertReflexivity =
    numericalSyntax.hilbertReflexivity ≫ formulaIso.hom := hilbertReflexivity
example : equalityIso.hom ≫ numericalInterpretation.map originalSyntax.hilbertEquality =
    numericalSyntax.hilbertEquality ≫ formulaIso.hom := hilbertEquality
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SchemeSquares.Checks
