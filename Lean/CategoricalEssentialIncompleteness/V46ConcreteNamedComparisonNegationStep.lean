/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonStateProjections
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonCanonicalCoordinates

/-! # The actual negation substitution step propagates the numeric option result -/

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
local notation "Y" => (syntaxCarrier V σ π d true : PredicateCategory T)

theorem negationSubstitutionPair_result_code (p : Obj T M P) (u param : M)
    (q : Obj T M (P ⨯ (S).substitutionCarriers.2))
    (hq : (stateLeaf T P V σ π d true).val.Evalb ![p.val,u,q.val]) :
    optionCode T M Y ((F T M).map (prod.snd : (S).substitutionCarriers.2 ⟶ _)
      ((F T M).map (prod.snd : P ⨯ (S).substitutionCarriers.2 ⟶ _)
        ((F T M).map ((constantFamilyFunctor P).map (S).negationSubstitutionPair).left q))) =
      ConcreteNamedSubstitution.result
        (ConcreteNamedSubstitution.formulaRoot V π d param (negationInput u)) := by
  let state := (F T M).map (prod.snd : P ⨯ (S).substitutionCarriers.2 ⟶ _) q
  let child := (F T M).map (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj Y) state
  have hp := model_map_snd T M (𝟙 P) (S).negationSubstitutionPair q
  have hs := model_lift_snd T M
    (prod.fst ≫ (S).negationConstructor : (S).substitutionCarriers.2 ⟶ Y)
    (prod.snd ≫ OptionSyntax.map (S).negationConstructor) state
  have hc : (F T M).map (prod.snd ≫ OptionSyntax.map (S).negationConstructor) state =
      (F T M).map (OptionSyntax.map (S).negationConstructor) child := by
    rw [Functor.map_comp_apply]
  have hpoint := (congrArg ((F T M).map (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj Y)) hp).trans
    (hs.trans hc)
  have hres := stateLeaf_formula_optionCode T P V σ π d M p u q hq
  have hm := optionCode_map T M (S).negationConstructor
    (fun value => Coding.constructor true (SyntaxPolynomial.formulaExpression V π d) (negationInput value))
    (fun value => negation_coordinate_value T V σ π d M value) child
  have hres' : optionCode T M Y child = ConcreteNamedSubstitution.result u := hres
  erw [hres'] at hm
  have ho := (congrArg (optionCode T M Y) hpoint).trans hm
  change optionCode T M Y ((F T M).map (prod.snd : (S).substitutionCarriers.2 ⟶ _)
    ((F T M).map (prod.snd : P ⨯ (S).substitutionCarriers.2 ⟶ _)
      ((F T M).map (prod.map (𝟙 P) (S).negationSubstitutionPair) q))) = _
  refine ho.trans ?_
  rw [formulaRoot_negation_result V π d param u]
  by_cases hs : π₂ (ConcreteNamedSubstitution.result u) = 1 <;>
    simp only [hs,↓reduceIte,ConcreteNamedSubstitution.ok]

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
