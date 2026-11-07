import CategoricalEssentialIncompleteness.V46NumericalArithmeticRules
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Rules.Checks
open Coordinates NamedArithmeticSignature
example (Γ : Carrier) : (rules Γ).instances 1 ≅ numericalInterpretation.obj ((originalRules Γ).instances 1) := rho1 Γ
example (Γ : Carrier) : (rules Γ).instances 2 ≅ numericalInterpretation.obj ((originalRules Γ).instances 2) := rho2 Γ
example (Γ : Carrier) :
    axioms Γ ≫ numericalSyntax.sentenceInclusion ≫ formulaIso.hom =
      numericalInterpretation.map (ArithmeticLiteralModel.axioms Γ ≫ originalSyntax.sentenceInclusion) := axioms_formula Γ
example (Γ : Carrier) :
    (rho2 Γ).hom ≫ numericalInterpretation.map
        (prod.snd : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance (Limits.prod (C := PredicateCategory 𝗣𝗔) originalSyntax.algebra.a.2 originalSyntax.algebra.a.2) originalSyntax.algebra.a.2) =
      prod.snd ≫ formulaIso.hom := rho2_conclusion Γ
example (Γ : Carrier) :
    (rho1 Γ).inv ≫ prod.snd ≫ formulaIso.hom =
      numericalInterpretation.map
        (prod.snd : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance (Limits.prod (C := PredicateCategory 𝗣𝗔) variableSymbols originalSyntax.algebra.a.2) originalSyntax.algebra.a.2) :=
  rho1_inverse_premise Γ
example (Γ : Carrier) :
    (rho2 Γ).inv ≫ prod.fst ≫ formulaIso.hom =
      numericalInterpretation.map
        (prod.fst : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance (Limits.prod (C := PredicateCategory 𝗣𝗔) originalSyntax.algebra.a.2 originalSyntax.algebra.a.2) originalSyntax.algebra.a.2) :=
  rho2_inverse_left Γ
example (Γ : Carrier) :
    (rho1 Γ).hom ≫ numericalInterpretation.map ((originalRules Γ).conclusion 1) =
      (rules Γ).conclusion 1 ≫ formulaIso.hom := rho1_rule_conclusion Γ
example (Γ : Carrier) :
    (rho1 Γ).hom ≫ numericalInterpretation.map ((originalRules Γ).premises 1) ≫
      (NumericalDerivationInterpretation.finitePowerIso originalSyntax.algebra.a.2 1).hom =
      (rules Γ).premises 1 ≫ finitePowerMap formulaIso.hom 1 := rho1_rule_premises Γ
example (Γ : Carrier) :
    (rho2 Γ).hom ≫ numericalInterpretation.map ((originalRules Γ).conclusion 2) =
      (rules Γ).conclusion 2 ≫ formulaIso.hom := rho2_rule_conclusion Γ
example (Γ : Carrier) :
    (rho2 Γ).hom ≫ numericalInterpretation.map ((originalRules Γ).premises 2) ≫
      (NumericalDerivationInterpretation.finitePowerIso originalSyntax.algebra.a.2 2).hom =
      (rules Γ).premises 2 ≫ finitePowerMap formulaIso.hom 2 := rho2_rule_premises Γ
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Rules.Checks
