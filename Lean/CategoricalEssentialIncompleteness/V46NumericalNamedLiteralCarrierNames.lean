/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralAlgorithms
import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralVariables
import CategoricalEssentialIncompleteness.V46NamedPostfixComparison

/-! # The coded numerical variable object has exactly the literal named words -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamed
open SyntacticSyntax SyntacticSyntax.Coding

section VariableCarriers
variable (V W : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (hVW : ∀ x : M, V.val.Evalb ![x] ↔ W.val.Evalb ![x])
include hVW

private theorem term_raw_variable_parameter (X Y : Carrier) (u : M) :
    (rawCarrier X Y (SyntaxPolynomial.termExpression V σ d)).val.Evalb ![u] ↔
      (rawCarrier X Y (SyntaxPolynomial.termExpression W σ d)).val.Evalb ![u] := by
  unfold SyntaxPolynomial.termExpression
  rw [rawCarrier_sum_eval, rawCarrier_sum_eval]
  simp only [rawCarrier, hVW]

private theorem formula_raw_variable_parameter (X Y : Carrier) (u : M) :
    (rawCarrier X Y (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![u] ↔
      (rawCarrier X Y (SyntaxPolynomial.formulaExpression W π d)).val.Evalb ![u] := by
  unfold SyntaxPolynomial.formulaExpression
  simp only [rawCarrier_sum_eval, rawCarrier_product_eval]
  simp only [rawCarrier, hVW]

private theorem record_variable_parameter (r : M) :
    (recordCarrier (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![r] ↔
    (recordCarrier (SyntaxPolynomial.termExpression W σ d)
      (SyntaxPolynomial.formulaExpression W π d)).val.Evalb ![r] := by
  simp only [recordCarrier_eval, term_raw_variable_parameter V W σ d hVW,
    formula_raw_variable_parameter V W π d hVW]

private theorem coefficients_variable_parameter (word : M) :
    (coefficients (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![word] ↔
    (coefficients (SyntaxPolynomial.termExpression W σ d)
      (SyntaxPolynomial.formulaExpression W π d)).val.Evalb ![word] := by
  rw [coefficients, ← FiniteSigmaOne.finite_membership_model,
    FiniteSigmaOne.allEntriesCondition_eval, coefficients,
    ← FiniteSigmaOne.finite_membership_model, FiniteSigmaOne.allEntriesCondition_eval]
  simp only [record_variable_parameter V W σ π d hVW]

omit hVW in
theorem parser_variable_parameter (word initial : M) :
    Postfix.run (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) word initial =
    Postfix.run (SyntaxPolynomial.termExpression W σ d)
      (SyntaxPolynomial.formulaExpression W π d) word initial := rfl

theorem plainCarrier_variable_parameter (formula : Bool) (word : M) :
    (Postfix.plainCarrier formula (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![word] ↔
    (Postfix.plainCarrier formula (SyntaxPolynomial.termExpression W σ d)
      (SyntaxPolynomial.formulaExpression W π d)).val.Evalb ![word] := by
  rw [Postfix.plainCarrier_eval, Postfix.plainCarrier_eval]
  exact and_congr (coefficients_variable_parameter V W σ π d hVW word)
    (by rw [parser_variable_parameter V W σ π d])

end VariableCarriers

theorem coded_plain_native (σ π : ℕ → Carrier) (d : ℕ) (formula : Bool) (word : ℕ) :
    (Postfix.plainCarrier formula
      (SyntaxPolynomial.termExpression (NumericalCoordinates.codedPredicate variableObject) σ d)
      (SyntaxPolynomial.formulaExpression (NumericalCoordinates.codedPredicate variableObject) π d)).val.Evalb ![word] ↔
    (Postfix.plainCarrier formula (NamedPostfixEncoding.termPolynomial σ d)
      (NamedPostfixEncoding.formulaPolynomial π d)).val.Evalb ![word] :=
  plainCarrier_variable_parameter (NumericalCoordinates.codedPredicate variableObject)
    NamedPostfixEncoding.variableCarrier σ π d codedVariable_literal formula word

end CategoricalEssentialIncompleteness.V46.NumericalNamed
