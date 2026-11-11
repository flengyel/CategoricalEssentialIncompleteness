/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonStateProjections
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonParameterProjections
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonCanonicalOperations
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonSubstitutionComponents

/-! # Actual result equations for the labelled function substitution branch -/

@[expose] public section

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
local notation "C" => SyntaxPolynomial.constructors σ d

theorem functionSubstitutionPair_result_value (p : Obj T M P) (u : M)
    (q : Obj T M (((C).withParameters P).eval.obj
      ((S).substitutionAlgebra.a)).left)
    (hq : (representation T P (S).substitutionAlgebra.a
      (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true) C).val.Evalb ![p.val,u,q.val]) :
    ((F T M).map (prod.snd : (S).algebra.a.1 ⨯ (S).algebra.a.1 ⟶ _)
      ((F T M).map (prod.snd : P ⨯ (S).substitutionCarriers.1 ⟶ _)
        ((F T M).map (SyntaxPolynomial.parameterComparison P (S).substitutionCarriers C ≫
          (constantFamilyFunctor P).map (S).functionSubstitutionPair).left q))).val =
      Coding.constructor false (SyntaxPolynomial.termExpression V σ d)
        (Arithmetic.pair (ConcreteNamedSubstitution.mapChildren ConcreteNamedSubstitution.result
          ConcreteNamedSubstitution.original C u) 1) := by
  let f := stateTermResultFamily T P V σ π d
  let g := stateOriginalFamily T P V σ π d true
  let j := ((C).withParameters P).eval.map ((f,g) :
    (S).substitutionAlgebra.a ⟶
      (constantFamily P (syntaxCarrier V σ π d false : PredicateCategory T),
        constantFamily P (syntaxCarrier V σ π d true : PredicateCategory T)))
  let z := (F T M).map j.left q
  let v := ConcreteNamedSubstitution.mapChildren ConcreteNamedSubstitution.result ConcreteNamedSubstitution.original C u
  have hz := stateResults_polynomialCoordinates T P V σ π d M p C u q hq
  have hr := parameterValueMap_representation T M P
    (syntaxCarrier V σ π d false) (syntaxCarrier V σ π d true) C p v z hz
  have hc := constant_projection_after_value T M
    (SyntaxPolynomial.parameterComparison P (S).substitutionCarriers C ≫
      (constantFamilyFunctor P).map (S).functionSubstitutionPair)
    (prod.snd : (S).algebra.a.1 ⨯ (S).algebra.a.1 ⟶ _)
    j (SyntaxPolynomial.parameterComparison P (S).algebra.a C ≫
      (constantFamilyFunctor P).map (S).functionConstructors)
    (functionSubstitution_result_component (S)) q
  have hp := parameterOperation_value T M P
    (syntaxCarrier V σ π d false) (syntaxCarrier V σ π d true) (syntaxCarrier V σ π d false)
    C (S).functionConstructors z
  have hv := CanonicalOperations.function_value T M V σ π d v
    ((F T M).map (parameterValueMap T P (syntaxCarrier V σ π d false)
      (syntaxCarrier V σ π d true) C) z) hr
  exact (congrArg Subtype.val hc).trans ((congrArg Subtype.val hp).trans hv)

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
