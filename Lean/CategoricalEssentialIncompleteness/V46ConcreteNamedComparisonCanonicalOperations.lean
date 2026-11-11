/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPlainOperationsModels
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonGraphs

/-! # Literal constructor values of the canonical computed syntax -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.NamedPlainOperationsModels
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.CanonicalOperations
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
local notation "S" => categoricalSyntax T V σ π d
local notation "X" => (syntaxCarrier V σ π d false : PredicateCategory T)
local notation "Y" => (syntaxCarrier V σ π d true : PredicateCategory T)
local notation "E" => SyntaxPolynomial.power (SyntaxPolynomial.term : SyntaxPolynomial (PredicateCategory T)) 2
local notation "R" => SyntaxPolynomial.constructors π d
local notation "I" => SyntaxPolynomial.power (SyntaxPolynomial.formula : SyntaxPolynomial (PredicateCategory T)) 2
local notation "Q" => SyntaxPolynomial.product (SyntaxPolynomial.coefficient V) SyntaxPolynomial.formula

/-- The actual variable constructor has the literal named-variable word
value at every interpreted point. -/
theorem variable_value (x : Obj T M V) :
    ((F T M).map (S).variableConstructor x).val =
      Coding.constructor false (SyntaxPolynomial.termExpression V σ d) (Arithmetic.pair x.val 0) := by
  have hx := (baseRepresentation_coefficient_eval T M X Y V x.val x.val).mpr
    ⟨x.property,rfl⟩
  have hi := representation_inl T M X Y (.coefficient V)
    (SyntaxPolynomial.constructors σ d) x.val x hx
  simp only [categoricalSyntax,CategoricalSyntax.variableConstructor,Functor.map_comp_apply]
  erw [postfixTerm_value T M (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) _ _ hi]

theorem negation_value (φ : Obj T M Y) :
    ((F T M).map (S).negationConstructor φ).val =
      Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
        (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair φ.val 1) 0) 0) := by
  have hφ := (baseRepresentation_formula_eval T M X Y φ.val φ.val).mpr ⟨φ.property,rfl⟩
  have h₁ := representation_inr T M X Y (.sum E R) .formula φ.val φ hφ
  have h₂ := representation_inl T M X Y (.sum (.sum E R) .formula) I _ _ h₁
  have h₃ := representation_inl T M X Y (.sum (.sum (.sum E R) .formula) I) Q _ _ h₂
  simp only [categoricalSyntax,CategoricalSyntax.negationConstructor,CategoricalSyntax.negationInjection,
    Functor.map_comp_apply]
  erw [postfixFormula_value T M
      (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d) _ _ h₃]

theorem implication_value (z : Obj T M (Y ⨯ Y)) :
    ((F T M).map (S).implicationConstructor z).val =
      Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
        (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair
          ((F T M).map (prod.fst (C := PredicateCategory T) («X» := Y) («Y» := Y)) z).val
          ((F T M).map (prod.snd (C := PredicateCategory T) («X» := Y) («Y» := Y)) z).val) 1) 0) := by
  have h₁ := representation_pair T M X Y .formula .formula _ _ z
    ((baseRepresentation_formula_eval T M X Y _ _).mpr
      ⟨((F T M).map (prod.fst (C := PredicateCategory T) («X» := Y) («Y» := Y)) z).property,rfl⟩)
    ((baseRepresentation_formula_eval T M X Y _ _).mpr
      ⟨((F T M).map (prod.snd (C := PredicateCategory T) («X» := Y) («Y» := Y)) z).property,rfl⟩)
  have h₂ := representation_inr T M X Y (.sum (.sum E R) .formula) I _ z h₁
  have h₃ := representation_inl T M X Y (.sum (.sum (.sum E R) .formula) I) Q _ _ h₂
  simp only [categoricalSyntax,CategoricalSyntax.implicationConstructor,Functor.map_comp_apply]
  erw [postfixFormula_value T M (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) _ _ h₃]
  all_goals rfl

theorem equality_value (z : Obj T M (X ⨯ X)) :
    ((F T M).map (S).equalityConstructor z).val =
      Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
        (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair
          ((F T M).map (prod.fst (C := PredicateCategory T) («X» := X) («Y» := X)) z).val
          ((F T M).map (prod.snd (C := PredicateCategory T) («X» := X) («Y» := X)) z).val) 0) 0) 0) 0) := by
  have h₁ := representation_pair T M X Y .term .term _ _ z
    ((baseRepresentation_term_eval T M X Y _ _).mpr
      ⟨((F T M).map (prod.fst (C := PredicateCategory T) («X» := X) («Y» := X)) z).property,rfl⟩)
    ((baseRepresentation_term_eval T M X Y _ _).mpr
      ⟨((F T M).map (prod.snd (C := PredicateCategory T) («X» := X) («Y» := X)) z).property,rfl⟩)
  have h₂ := representation_inl T M X Y E R _ z h₁
  have h₃ := representation_inl T M X Y (.sum E R) .formula _ _ h₂
  have h₄ := representation_inl T M X Y (.sum (.sum E R) .formula) I _ _ h₃
  have h₅ := representation_inl T M X Y (.sum (.sum (.sum E R) .formula) I) Q _ _ h₄
  simp only [categoricalSyntax,CategoricalSyntax.equalityConstructor,Functor.map_comp_apply]
  erw [postfixFormula_value T M (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) _ _ h₅]
  all_goals rfl

theorem quantifier_value (z : Obj T M (V ⨯ Y)) :
    ((F T M).map (S).quantifierConstructor z).val =
      Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
        (Arithmetic.pair (Arithmetic.pair
          ((F T M).map (prod.fst : V ⨯ Y ⟶ _) z).val
          ((F T M).map (prod.snd : V ⨯ Y ⟶ _) z).val) 1) := by
  have h₁ := representation_pair T M X Y (.coefficient V) .formula _ _ z
    ((baseRepresentation_coefficient_eval T M X Y V _ _).mpr
      ⟨((F T M).map (prod.fst : V ⨯ Y ⟶ _) z).property,rfl⟩)
    ((baseRepresentation_formula_eval T M X Y _ _).mpr
      ⟨((F T M).map (prod.snd : V ⨯ Y ⟶ _) z).property,rfl⟩)
  have h₂ := representation_inr T M X Y (.sum (.sum (.sum E R) .formula) I) Q _ z h₁
  simp only [categoricalSyntax,CategoricalSyntax.quantifierConstructor,Functor.map_comp_apply]
  erw [postfixFormula_value T M (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) _ _ h₂]
  all_goals rfl

theorem function_value (u : M)
    (z : Obj T M ((SyntaxPolynomial.constructors σ d).eval.obj (S).algebra.a))
    (hz : (baseRepresentation T X Y (SyntaxPolynomial.constructors σ d)).val.Evalb ![u,z.val]) :
    ((F T M).map (S).functionConstructors z).val =
      Coding.constructor false (SyntaxPolynomial.termExpression V σ d) (Arithmetic.pair u 1) := by
  have hi := representation_inr T M X Y (.coefficient V) (SyntaxPolynomial.constructors σ d) u z hz
  simp only [categoricalSyntax,CategoricalSyntax.functionConstructors,Functor.map_comp_apply]
  erw [postfixTerm_value T M (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d) _ _ hi]

theorem relation_value (u : M)
    (z : Obj T M ((SyntaxPolynomial.constructors π d).eval.obj (S).algebra.a))
    (hz : (baseRepresentation T X Y (SyntaxPolynomial.constructors π d)).val.Evalb ![u,z.val]) :
    ((F T M).map (S).relationConstructors z).val =
      Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
        (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair u 1) 0) 0) 0) := by
  have h₁ := representation_inr T M X Y E R u z hz
  have h₂ := representation_inl T M X Y (.sum E R) .formula _ _ h₁
  have h₃ := representation_inl T M X Y (.sum (.sum E R) .formula) I _ _ h₂
  have h₄ := representation_inl T M X Y (.sum (.sum (.sum E R) .formula) I) Q _ _ h₃
  simp only [categoricalSyntax,CategoricalSyntax.relationConstructors,Functor.map_comp_apply]
  erw [postfixFormula_value T M (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d) _ _ h₄]

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.CanonicalOperations
