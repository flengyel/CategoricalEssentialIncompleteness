/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonStateProjections
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonParameterProjections
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonParameterSomeValues
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonCanonicalCoordinates
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonSubstitutionComponents

/-! # Actual equality/relation substitution results on ordered child states -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local notation "S" => categoricalSyntax T V σ π d
local notation "P" => CategoricalSyntax.substitutionParameters (categoricalSyntax T V σ π d)
local notation "X" => (syntaxCarrier V σ π d false : PredicateCategory T)
local notation "Y" => (syntaxCarrier V σ π d true : PredicateCategory T)
local notation "E" => SyntaxPolynomial.power (SyntaxPolynomial.term : SyntaxPolynomial (PredicateCategory T)) 2
local notation "R" => SyntaxPolynomial.constructors π d

theorem equalitySubstitutionPair_result_code (p : Obj T M P) (u : M)
    (q : Obj T M (((E).withParameters P).eval.obj (S).substitutionAlgebra.a).left)
    (hq : (representation T P (S).substitutionAlgebra.a
      (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true) E).val.Evalb ![p.val,u,q.val]) :
    optionCode T M Y ((F T M).map (prod.snd : (S).substitutionCarriers.2 ⟶ _)
      ((F T M).map (prod.snd : P ⨯ (S).substitutionCarriers.2 ⟶ _)
        ((F T M).map (SyntaxPolynomial.parameterComparison P (S).substitutionCarriers E ≫
          (constantFamilyFunctor P).map (S).equalitySubstitutionPair).left q))) =
      ConcreteNamedSubstitution.ok (Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
        (equalityInput (ConcreteNamedSubstitution.mapChildren ConcreteNamedSubstitution.result
          ConcreteNamedSubstitution.original E u))) := by
  let j := ((E).withParameters P).eval.map
    ((stateTermResultFamily T P V σ π d,stateOriginalFamily T P V σ π d true) :
      (S).substitutionAlgebra.a ⟶ (constantFamily P X,constantFamily P Y))
  let z := (F T M).map j.left q
  let v := ConcreteNamedSubstitution.mapChildren ConcreteNamedSubstitution.result ConcreteNamedSubstitution.original E u
  have hz := stateResults_polynomialCoordinates T P V σ π d M p E u q hq
  have hc := constant_projection_after_value T M
    (SyntaxPolynomial.parameterComparison P (S).substitutionCarriers E ≫
      (constantFamilyFunctor P).map (S).equalitySubstitutionPair)
    (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj Y)
    j (SyntaxPolynomial.parameterComparison P (S).algebra.a E ≫
      (constantFamilyFunctor P).map ((S).equalityConstructor ≫ coprod.inr))
    (equalitySubstitution_result_component (S)) q
  have hp := parameterOperation_some_code T M P X Y Y E (S).equalityConstructor
    (fun w => Coding.constructor true (SyntaxPolynomial.formulaExpression V π d) (equalityInput w))
    (fun w z hz => equality_coordinate_value T V σ π d M w z hz) p v z hz
  exact (congrArg (optionCode T M Y) hc).trans hp

theorem relationSubstitutionPair_result_code (p : Obj T M P) (u : M)
    (q : Obj T M (((R).withParameters P).eval.obj (S).substitutionAlgebra.a).left)
    (hq : (representation T P (S).substitutionAlgebra.a
      (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true) R).val.Evalb ![p.val,u,q.val]) :
    optionCode T M Y ((F T M).map (prod.snd : (S).substitutionCarriers.2 ⟶ _)
      ((F T M).map (prod.snd : P ⨯ (S).substitutionCarriers.2 ⟶ _)
        ((F T M).map (SyntaxPolynomial.parameterComparison P (S).substitutionCarriers R ≫
          (constantFamilyFunctor P).map (S).relationSubstitutionPair).left q))) =
      ConcreteNamedSubstitution.ok (Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
        (relationInput (ConcreteNamedSubstitution.mapChildren ConcreteNamedSubstitution.result
          ConcreteNamedSubstitution.original R u))) := by
  let j := ((R).withParameters P).eval.map
    ((stateTermResultFamily T P V σ π d,stateOriginalFamily T P V σ π d true) :
      (S).substitutionAlgebra.a ⟶ (constantFamily P X,constantFamily P Y))
  let z := (F T M).map j.left q
  let v := ConcreteNamedSubstitution.mapChildren ConcreteNamedSubstitution.result ConcreteNamedSubstitution.original R u
  have hz := stateResults_polynomialCoordinates T P V σ π d M p R u q hq
  have hc := constant_projection_after_value T M
    (SyntaxPolynomial.parameterComparison P (S).substitutionCarriers R ≫
      (constantFamilyFunctor P).map (S).relationSubstitutionPair)
    (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj Y)
    j (SyntaxPolynomial.parameterComparison P (S).algebra.a R ≫
      (constantFamilyFunctor P).map ((S).relationConstructors ≫ coprod.inr))
    (relationSubstitution_result_component (S)) q
  have hp := parameterOperation_some_code T M P X Y Y R (S).relationConstructors
    (fun w => Coding.constructor true (SyntaxPolynomial.formulaExpression V π d) (relationInput w))
    (fun w z hz => relation_coordinate_value T V σ π d M w z hz) p v z hz
  exact (congrArg (optionCode T M Y) hc).trans hp

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
