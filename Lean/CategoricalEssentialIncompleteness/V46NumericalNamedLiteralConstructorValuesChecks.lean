/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralConstructorValues


/-! # Statement checks in `V46NumericalNamedLiteralConstructorValuesChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralConstructorValuesChecks
open NumericalNamed
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "S" => literalCategoricalSyntax V σ π d
local notation "a" => SyntaxPolynomial.termExpression (NumericalCoordinates.codedPredicate V)
  (fun n => NumericalCoordinates.codedPredicate (σ n)) d
local notation "b" => SyntaxPolynomial.formulaExpression (NumericalCoordinates.codedPredicate V)
  (fun n => NumericalCoordinates.codedPredicate (π n)) d

example (x : NumericalTuples.Point ((SyntaxPolynomial.termExpression V σ d).eval.obj (S).algebra.a)) :
    ((literalTermPresentationIso V σ π d).hom.toFun ((S).algebra.str.1.toFun x)).val =
      SyntacticSyntax.Coding.constructor false (a)
        (((F 𝗧𝗔 ℕ).map (NumericalSyntaxTreeChart.plainRawInput 𝗧𝗔 (a) (b)))
          ((literalTermConstructorInputPresentationIso V σ π d).hom.toFun x)).val :=
  literal_termConstructor_value V σ π d x
example (x : NumericalTuples.Point ((SyntaxPolynomial.formulaExpression V π d).eval.obj (S).algebra.a)) :
    ((literalFormulaPresentationIso V σ π d).hom.toFun ((S).algebra.str.2.toFun x)).val =
      SyntacticSyntax.Coding.constructor true (b)
        (((F 𝗧𝗔 ℕ).map (plainFormulaRawInput 𝗧𝗔 (a) (b)))
          ((literalFormulaConstructorInputPresentationIso V σ π d).hom.toFun x)).val :=
  literal_formulaConstructor_value V σ π d x

end CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralConstructorValuesChecks
