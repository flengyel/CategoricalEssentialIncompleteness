/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPlainOperationsModels


/-! # Literal values of the concrete plain logical constructors -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainOperationsModelsChecks
open SyntacticSyntax NamedPlainOperationsModels
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
local notation "S" => plainCategoricalSyntax T V σ π d
local notation "X" => (Postfix.plainCarrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d) : PredicateCategory T)
local notation "Y" => (Postfix.plainCarrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d) : PredicateCategory T)
example (x : Obj T M V) :
    ((F T M).map (S).variableConstructor x).val =
      Coding.constructor false (SyntaxPolynomial.termExpression V σ d) (Arithmetic.pair x.val 0) :=
  variable_value T M V σ π d x
example (φ : Obj T M Y) :
    ((F T M).map (S).negationConstructor φ).val =
      Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
        (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair φ.val 1) 0) 0) :=
  negation_value T M V σ π d φ
example (z : Obj T M (Y ⨯ Y)) :
    ((F T M).map (S).implicationConstructor z).val =
      Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
        (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair
          ((F T M).map (prod.fst (C := PredicateCategory T) («X» := Y) («Y» := Y)) z).val
          ((F T M).map (prod.snd (C := PredicateCategory T) («X» := Y) («Y» := Y)) z).val) 1) 0) :=
  implication_value T M V σ π d z
example (z : Obj T M (X ⨯ X)) :
    ((F T M).map (S).equalityConstructor z).val =
      Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
        (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair
          ((F T M).map (prod.fst (C := PredicateCategory T) («X» := X) («Y» := X)) z).val
          ((F T M).map (prod.snd (C := PredicateCategory T) («X» := X) («Y» := X)) z).val) 0) 0) 0) 0) :=
  equality_value T M V σ π d z
example (z : Obj T M (V ⨯ Y)) :
    ((F T M).map (S).quantifierConstructor z).val =
      Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
        (Arithmetic.pair (Arithmetic.pair
          ((F T M).map (prod.fst : V ⨯ Y ⟶ _) z).val
          ((F T M).map (prod.snd : V ⨯ Y ⟶ _) z).val) 1) :=
  quantifier_value T M V σ π d z
end CategoricalEssentialIncompleteness.V46.NamedPlainOperationsModelsChecks
