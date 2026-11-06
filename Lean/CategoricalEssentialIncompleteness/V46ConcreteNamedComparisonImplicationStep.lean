/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonStateProjections
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonCanonicalCoordinates
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonParameterPoints
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonRelationPoints
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonOptionBranches

/-! # The actual implication substitution step has the numeric failure/success rule -/

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
local notation "I" => SyntaxPolynomial.power (SyntaxPolynomial.formula : SyntaxPolynomial (PredicateCategory T)) 2

theorem implicationSubstitutionPair_result_code (p : Obj T M P) (u param : M)
    (q : Obj T M (((I).withParameters P).eval.obj (S).substitutionAlgebra.a).left)
    (hq : (representation T P (S).substitutionAlgebra.a
      (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true) I).val.Evalb ![p.val,u,q.val]) :
    optionCode T M Y ((F T M).map (prod.snd : (S).substitutionCarriers.2 ⟶ _)
      ((F T M).map (prod.snd : P ⨯ (S).substitutionCarriers.2 ⟶ _)
        ((F T M).map (SyntaxPolynomial.parameterComparison P (S).substitutionCarriers I ≫
          (constantFamilyFunctor P).map (S).implicationSubstitutionPair).left q))) =
      ConcreteNamedSubstitution.result
        (ConcreteNamedSubstitution.formulaRoot V π d param (implicationInput u)) := by
  let C := constantFamily P (S).substitutionCarriers.2
  let ql := (F T M).map (prod.fst : C ⨯ C ⟶ C).left q
  let qr := (F T M).map (prod.snd : C ⨯ C ⟶ C).left q
  obtain ⟨l,r,hu,hl,hr⟩ := relation_product_points T M P (S).substitutionAlgebra.a
    (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true) .formula .formula p.val u q hq
  let base := (F T M).map (parameterValueMap T P (S).substitutionCarriers.1
    (S).substitutionCarriers.2 I) q
  let choices := (F T M).map
    (prod.map (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj Y) prod.snd) base
  have hbl := (parameterPoint_product_fst T M P (S).substitutionCarriers.1
    (S).substitutionCarriers.2 .formula .formula q).trans
      (parameterPoint_formula T M P (S).substitutionCarriers.1 (S).substitutionCarriers.2 ql)
  have hbr := (parameterPoint_product_snd T M P (S).substitutionCarriers.1
    (S).substitutionCarriers.2 .formula .formula q).trans
      (parameterPoint_formula T M P (S).substitutionCarriers.1 (S).substitutionCarriers.2 qr)
  have hcl := (model_map_fst T M
    (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj Y) prod.snd base).trans
      (congrArg ((F T M).map (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj Y)) hbl)
  have hcr := (model_map_snd T M
    (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj Y) prod.snd base).trans
      (congrArg ((F T M).map (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj Y)) hbr)
  have hcodeL := (congrArg (optionCode T M Y) hcl).trans
    (stateLeaf_formula_optionCode T P V σ π d M p l ql hl)
  have hcodeR := (congrArg (optionCode T M Y) hcr).trans
    (stateLeaf_formula_optionCode T P V σ π d M p r qr hr)
  have hp := parameterOperation_value T M P (S).substitutionCarriers.1
    (S).substitutionCarriers.2 (S).substitutionCarriers.2 I (S).implicationSubstitutionPair q
  have hs := model_lift_snd T M
    (prod.map (prod.fst : (S).substitutionCarriers.2 ⟶ Y) prod.fst ≫ (S).implicationConstructor)
    (prod.map (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj Y) prod.snd ≫
      OptionSyntax.binary (S).implicationConstructor) base
  have hc : (F T M).map
      (prod.map (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj Y) prod.snd ≫
        OptionSyntax.binary (S).implicationConstructor) base =
      (F T M).map (OptionSyntax.binary (S).implicationConstructor) choices := by
    rw [Functor.map_comp_apply]
  have hpoint := (congrArg ((F T M).map (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj Y)) hp).trans
    (hs.trans hc)
  have hm := optionCode_binary T M (S).implicationConstructor
    (fun x y => Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
      (implicationInput (Arithmetic.pair x y)))
    (fun z => CanonicalOperations.implication_value T M V σ π d z) choices
  erw [hcodeL,hcodeR] at hm
  have ho := (congrArg (optionCode T M Y) hpoint).trans hm
  change optionCode T M Y ((F T M).map (prod.snd : (S).substitutionCarriers.2 ⟶ _)
    ((F T M).map (prod.snd : P ⨯ (S).substitutionCarriers.2 ⟶ _)
      ((F T M).map (SyntaxPolynomial.parameterComparison P
        ((S).substitutionCarriers.1,(S).substitutionCarriers.2) I ≫
          (constantFamilyFunctor P).map (S).implicationSubstitutionPair).left q))) = _
  refine ho.trans ?_
  rw [formulaRoot_implication_result V π d param u,hu,pi₁_pair,pi₂_pair]
  by_cases hl : π₂ (ConcreteNamedSubstitution.result l) = 1 <;>
    by_cases hr : π₂ (ConcreteNamedSubstitution.result r) = 1 <;>
      simp only [hl,hr,ConcreteNamedSubstitution.ok]

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
