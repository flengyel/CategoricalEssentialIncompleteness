/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticAlgorithms


/-! # Arithmetic algorithms are independent of coefficient guards -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Algorithms.Checks
open ConcreteNamedSubstitution SyntacticSyntax SyntacticSyntax.Coding
variable (V W : Carrier) (σ τ π ρ : ℕ → Carrier) (d : ℕ)
example (b : Bool) : constructorGraph b (SyntaxPolynomial.termExpression V σ d) =
    constructorGraph b (SyntaxPolynomial.termExpression W τ d) :=
  termConstructorGraph_signature V W σ τ d b
example (b : Bool) : constructorGraph b (SyntaxPolynomial.formulaExpression V π d) =
    constructorGraph b (SyntaxPolynomial.formulaExpression W ρ d) :=
  formulaConstructorGraph_signature V W π ρ d b
example : freeVariablesGraph V σ π d = freeVariablesGraph W τ ρ d :=
  freeVariablesGraph_signature V W σ τ π ρ d
example : substitutionResultGraph V σ π d = substitutionResultGraph W τ ρ d :=
  substitutionResultGraph_signature V W σ τ π ρ d
example : substitutionFreeForGraph V σ π d = substitutionFreeForGraph W τ ρ d :=
  substitutionFreeForGraph_signature V W σ τ π ρ d
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example (b : Bool) (u : M) : constructor b (SyntaxPolynomial.termExpression V σ d) u =
    constructor b (SyntaxPolynomial.termExpression W τ d) u :=
  termConstructor_signature V W σ τ d b u
example (b : Bool) (u : M) : constructor b (SyntaxPolynomial.formulaExpression V π d) u =
    constructor b (SyntaxPolynomial.formulaExpression W ρ d) u :=
  formulaConstructor_signature V W π ρ d b u
example (word : M) : freeVariables V σ π d word = freeVariables W τ ρ d word :=
  freeVariables_signature V W σ τ π ρ d word
example (x replacement word : M) :
    substitutionPayload V σ π d x replacement word = substitutionPayload W τ ρ d x replacement word :=
  substitutionPayload_signature V W σ τ π ρ d x replacement word
example (x replacement word : M) :
    substitutionResult V σ π d x replacement word = substitutionResult W τ ρ d x replacement word :=
  substitutionResult_signature V W σ τ π ρ d x replacement word
example (x replacement word : M) :
    substitutionFreeFor V σ π d x replacement word = substitutionFreeFor W τ ρ d x replacement word :=
  substitutionFreeFor_signature V W σ τ π ρ d x replacement word
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Algorithms.Checks
