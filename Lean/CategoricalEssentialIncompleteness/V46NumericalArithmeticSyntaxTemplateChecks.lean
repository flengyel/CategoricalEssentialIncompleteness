/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticSyntaxTemplate


/-! # Statement checks in `V46NumericalArithmeticSyntaxTemplateChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SyntaxTemplate.Checks
open Coordinates SyntacticSyntax
example (i : Label) (z : Obj 𝗣𝗔 ℕ (source i)) :
    ((NumericalCoordinates.predicatePresentationIso (target i)).hom.toFun
      ((coefficientChart i).hom.toFun z)).val = z.val := coefficient_value i z
example (u : ℕ) (z : Obj 𝗣𝗔 ℕ (sourceTerm.eval.obj originalSyntax.algebra.a)) :
    (baseRepresentation 𝗣𝗔 originalSyntax.algebra.a.1 originalSyntax.algebra.a.2 sourceTerm).val.Evalb ![u,z.val] ↔
      (baseRepresentation 𝗧𝗔 sourceSyntax.algebra.a.1 sourceSyntax.algebra.a.2 targetTerm).val.Evalb ![u,(termInput z).val] :=
  term_representation u z
example (u : ℕ) (z : Obj 𝗣𝗔 ℕ (sourceFormula.eval.obj originalSyntax.algebra.a)) :
    (baseRepresentation 𝗣𝗔 originalSyntax.algebra.a.1 originalSyntax.algebra.a.2 sourceFormula).val.Evalb ![u,z.val] ↔
      (baseRepresentation 𝗧𝗔 sourceSyntax.algebra.a.1 sourceSyntax.algebra.a.2 targetFormula).val.Evalb ![u,(formulaInput z).val] :=
  formula_representation u z
example : numericalInterpretation.map originalSyntax.algebra.str.1 ≫ termChart.hom =
    termInputIso.hom ≫ NumericalSyntaxTreeChart.E.functor.map sourceSyntax.algebra.str.1 := term_constructor
example : numericalInterpretation.map originalSyntax.algebra.str.2 ≫ formulaChart.hom =
    formulaInputIso.hom ≫ NumericalSyntaxTreeChart.E.functor.map sourceSyntax.algebra.str.2 := formula_constructor
example : numericalInterpretation.map originalSyntax.algebra.str.1 ≫ termIso.inv =
    numericalTermInputIso.hom ≫ numericalSyntax.algebra.str.1 := numerical_term_constructor
example : numericalInterpretation.map originalSyntax.algebra.str.2 ≫ formulaIso.inv =
    numericalFormulaInputIso.hom ≫ numericalSyntax.algebra.str.2 := numerical_formula_constructor
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SyntaxTemplate.Checks
