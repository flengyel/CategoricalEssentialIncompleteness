/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonCanonicalOperations
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonFormulaRootArithmetic
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonRepresentation

/-! # Canonical logical constructor values at the ordered raw coordinates -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local notation "S" => categoricalSyntax T V σ π d
local notation "X" => (syntaxCarrier V σ π d false : PredicateCategory T)
local notation "Y" => (syntaxCarrier V σ π d true : PredicateCategory T)

theorem equality_coordinate_value (u : M) (z : Obj T M (X ⨯ X))
    (hz : (baseRepresentation T X Y (SyntaxPolynomial.power .term 2)).val.Evalb ![u,z.val]) :
    ((F T M).map (S).equalityConstructor z).val =
      Coding.constructor true (SyntaxPolynomial.formulaExpression V π d) (equalityInput u) := by
  obtain ⟨l,r,he,hl,hr⟩ := representation_product_points T M X Y .term .term u z hz
  have h₁ := (baseRepresentation_term_eval T M X Y l
    ((F T M).map (prod.fst (C := PredicateCategory T) («X» := X) («Y» := X)) z).val).mp hl
  have h₂ := (baseRepresentation_term_eval T M X Y r
    ((F T M).map (prod.snd (C := PredicateCategory T) («X» := X) («Y» := X)) z).val).mp hr
  rw [← h₁.2,← h₂.2] at he
  exact (CanonicalOperations.equality_value T M V σ π d z).trans
    (congrArg (fun v => Coding.constructor true (SyntaxPolynomial.formulaExpression V π d) (equalityInput v)) he.symm)

theorem relation_coordinate_value (u : M)
    (z : Obj T M ((SyntaxPolynomial.constructors π d).eval.obj (S).algebra.a))
    (hz : (baseRepresentation T X Y (SyntaxPolynomial.constructors π d)).val.Evalb ![u,z.val]) :
    ((F T M).map (S).relationConstructors z).val =
      Coding.constructor true (SyntaxPolynomial.formulaExpression V π d) (relationInput u) :=
  CanonicalOperations.relation_value T M V σ π d u z hz

theorem negation_coordinate_value (z : Obj T M Y) :
    ((F T M).map (S).negationConstructor z).val =
      Coding.constructor true (SyntaxPolynomial.formulaExpression V π d) (negationInput z.val) :=
  CanonicalOperations.negation_value T M V σ π d z

theorem implication_coordinate_value (u : M) (z : Obj T M (Y ⨯ Y))
    (hz : (baseRepresentation T X Y (SyntaxPolynomial.power .formula 2)).val.Evalb ![u,z.val]) :
    ((F T M).map (S).implicationConstructor z).val =
      Coding.constructor true (SyntaxPolynomial.formulaExpression V π d) (implicationInput u) := by
  obtain ⟨l,r,he,hl,hr⟩ := representation_product_points T M X Y .formula .formula u z hz
  have h₁ := (baseRepresentation_formula_eval T M X Y l
    ((F T M).map (prod.fst (C := PredicateCategory T) («X» := Y) («Y» := Y)) z).val).mp hl
  have h₂ := (baseRepresentation_formula_eval T M X Y r
    ((F T M).map (prod.snd (C := PredicateCategory T) («X» := Y) («Y» := Y)) z).val).mp hr
  rw [← h₁.2,← h₂.2] at he
  exact (CanonicalOperations.implication_value T M V σ π d z).trans
    (congrArg (fun v => Coding.constructor true (SyntaxPolynomial.formulaExpression V π d) (implicationInput v)) he.symm)

theorem quantifier_coordinate_value (u : M) (z : Obj T M (V ⨯ Y))
    (hz : (baseRepresentation T X Y (.product (.coefficient V) .formula)).val.Evalb ![u,z.val]) :
    ((F T M).map (S).quantifierConstructor z).val =
      Coding.constructor true (SyntaxPolynomial.formulaExpression V π d) (quantifierInput u) := by
  obtain ⟨l,r,he,hl,hr⟩ := representation_product_points T M X Y (.coefficient V) .formula u z hz
  have h₁ := (baseRepresentation_coefficient_eval T M X Y V l
    ((F T M).map (prod.fst (C := PredicateCategory T) («X» := V) («Y» := Y)) z).val).mp hl
  have h₂ := (baseRepresentation_formula_eval T M X Y r
    ((F T M).map (prod.snd (C := PredicateCategory T) («X» := V) («Y» := Y)) z).val).mp hr
  rw [← h₁.2,← h₂.2] at he
  exact (CanonicalOperations.quantifier_value T M V σ π d z).trans
    (congrArg (fun v => Coding.constructor true (SyntaxPolynomial.formulaExpression V π d) (quantifierInput v)) he.symm)

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
