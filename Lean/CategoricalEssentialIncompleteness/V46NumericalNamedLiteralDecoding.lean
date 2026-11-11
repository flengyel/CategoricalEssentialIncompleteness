/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralCarrierNames
public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralOperations

/-! # Numerical word charts decode to the literal named finite syntax -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamed
open SyntacticSyntax
variable (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "σ₀" => (fun n => NumericalCoordinates.codedPredicate (σ n))
local notation "π₀" => (fun n => NumericalCoordinates.codedPredicate (π n))
local notation "S" => literalCategoricalSyntax variableObject σ π d

theorem literal_term_decodes (x : NumericalTuples.Point (S).algebra.a.1) :
    ∃ r : NamedFiniteSyntax.Term (NamedPostfixEncoding.Symbols σ₀) d,
      NamedPostfixEncoding.termCode r =
        ((literalTermPresentationIso variableObject σ π d).hom.toFun x).val := by
  let w : PredicateInterpretation.Obj ℕ (literalSourceSyntax variableObject σ π d).algebra.a.1 :=
    (literalTermPresentationIso variableObject σ π d).hom.toFun x
  have hw := w.property
  change (Postfix.plainCarrier false
    (SyntaxPolynomial.termExpression (NumericalCoordinates.codedPredicate variableObject) σ₀ d)
    (SyntaxPolynomial.formulaExpression (NumericalCoordinates.codedPredicate variableObject) π₀ d)).val.Evalb (M := ℕ) ![w.val] at hw
  exact (NamedPostfixEncoding.standard_codes_surjective σ₀ π₀ d).1 w.val
    ((Postfix.carrier_plain_model (M := ℕ) false (NamedPostfixEncoding.termPolynomial σ₀ d)
      (NamedPostfixEncoding.formulaPolynomial π₀ d) w.val).mpr
        ((coded_plain_native σ₀ π₀ d false w.val).mp hw))

theorem literal_formula_decodes (x : NumericalTuples.Point (S).algebra.a.2) :
    ∃ φ : NamedFiniteSyntax.Formula (NamedPostfixEncoding.Symbols σ₀)
        (NamedPostfixEncoding.Symbols π₀) d,
      NamedPostfixEncoding.formulaCode φ =
        ((literalFormulaPresentationIso variableObject σ π d).hom.toFun x).val := by
  let w : PredicateInterpretation.Obj ℕ (literalSourceSyntax variableObject σ π d).algebra.a.2 :=
    (literalFormulaPresentationIso variableObject σ π d).hom.toFun x
  have hw := w.property
  change (Postfix.plainCarrier true
    (SyntaxPolynomial.termExpression (NumericalCoordinates.codedPredicate variableObject) σ₀ d)
    (SyntaxPolynomial.formulaExpression (NumericalCoordinates.codedPredicate variableObject) π₀ d)).val.Evalb (M := ℕ) ![w.val] at hw
  exact (NamedPostfixEncoding.standard_codes_surjective σ₀ π₀ d).2 w.val
    ((Postfix.carrier_plain_model (M := ℕ) true (NamedPostfixEncoding.termPolynomial σ₀ d)
      (NamedPostfixEncoding.formulaPolynomial π₀ d) w.val).mpr
        ((coded_plain_native σ₀ π₀ d true w.val).mp hw))

end CategoricalEssentialIncompleteness.V46.NumericalNamed
