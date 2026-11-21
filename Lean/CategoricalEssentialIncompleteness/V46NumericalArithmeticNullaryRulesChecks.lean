/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticNullaryRules


/-! # The seven-scheme and Gamma nullary label isomorphism -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.NullaryRules.Checks
open Coordinates
example : numericalSyntax.logicalParameters ≅ numericalInterpretation.obj originalSyntax.logicalParameters := logicalIso
example : logicalIso.hom ≫ numericalInterpretation.map originalSyntax.logicalAxioms =
    numericalSyntax.logicalAxioms ≫ formulaIso.hom := logical_square
example (Γ : Carrier) : (Rules.rules Γ).instances 0 ≅ numericalInterpretation.obj ((Rules.originalRules Γ).instances 0) := rho0 Γ
example (Γ : Carrier) : (rho0 Γ).hom ≫ numericalInterpretation.map ((Rules.originalRules Γ).conclusion 0) =
    (Rules.rules Γ).conclusion 0 ≫ formulaIso.hom := rho0_rule_conclusion Γ
example (Γ : Carrier) :
    (rho0 Γ).hom ≫ numericalInterpretation.map ((Rules.originalRules Γ).premises 0) ≫
      (NumericalDerivationInterpretation.finitePowerIso originalSyntax.algebra.a.2 0).hom =
      (Rules.rules Γ).premises 0 ≫ finitePowerMap formulaIso.hom 0 := rho0_rule_premises Γ
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.NullaryRules.Checks
