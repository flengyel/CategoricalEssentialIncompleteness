/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPostfixSubstitution

/-! # Coefficient membership does not change the literal traversal algorithm -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamed
open SyntacticSyntax SyntacticSyntax.Coding ConcreteNamedSubstitution
variable (V W : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- The coefficient predicates guard labels separately. The constructor
itself retains the literal label and every ordered child word. -/
theorem term_constructor_variable_parameter (u : M) :
    constructor false (SyntaxPolynomial.termExpression V σ d) u =
      constructor false (SyntaxPolynomial.termExpression W σ d) u := rfl

theorem formula_constructor_variable_parameter (u : M) :
    constructor true (SyntaxPolynomial.formulaExpression V π d) u =
      constructor true (SyntaxPolynomial.formulaExpression W π d) u := rfl

theorem term_refill_variable_parameter (shape stack : M) :
    refill (SyntaxPolynomial.termExpression V σ d) shape stack =
      refill (SyntaxPolynomial.termExpression W σ d) shape stack := rfl

theorem formula_refill_variable_parameter (shape stack : M) :
    refill (SyntaxPolynomial.formulaExpression V π d) shape stack =
      refill (SyntaxPolynomial.formulaExpression W π d) shape stack := rfl

theorem termRoot_variable_parameter (param value : M) :
    termRoot V σ d param value = termRoot W σ d param value := rfl

theorem formulaRoot_variable_parameter (param value : M) :
    formulaRoot V π d param value = formulaRoot W π d param value := rfl

theorem freeVariables_variable_parameter (word : M) :
    freeVariables V σ π d word = freeVariables W σ π d word := rfl

theorem substitutionPayload_variable_parameter (x replacement word : M) :
    substitutionPayload V σ π d x replacement word =
      substitutionPayload W σ π d x replacement word := rfl

theorem substitutionResult_variable_parameter (x replacement word : M) :
    substitutionResult V σ π d x replacement word =
      substitutionResult W σ π d x replacement word := rfl

theorem substitutionFreeFor_variable_parameter (x replacement word : M) :
    substitutionFreeFor V σ π d x replacement word =
      substitutionFreeFor W σ π d x replacement word := rfl

end CategoricalEssentialIncompleteness.V46.NumericalNamed
