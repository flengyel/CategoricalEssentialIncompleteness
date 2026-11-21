/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonFormulaStep
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonCandidateOriginal

/-! # The computed formula-state morphism commutes with the full formula structure -/

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
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
local notation "S" => categoricalSyntax T V σ π d
local notation "A₀" => projectionSourceAlgebra T V V σ π d
local notation "P" => CategoricalSyntax.substitutionParameters (categoricalSyntax T V σ π d)
local notation "a" => SyntaxPolynomial.termExpression V σ d
local notation "b" => SyntaxPolynomial.formulaExpression V π d

theorem computedFormula_commutes_model
    (q : Obj T M (((b).withParameters P).eval.obj (A₀).a).left) :
    (F T M).map (S).substitutionAlgebra.str.2.left
      ((F T M).map (((b).withParameters P).eval.map (computedStatePair T V σ π d)).left q) =
      (F T M).map (computedStatePair T V σ π d).2.left
        ((F T M).map (A₀).str.2.left q) := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  let p := (F T M).map (((b).withParameters P).eval.obj (A₀).a).hom q
  obtain ⟨u,hu⟩ := constantRepresentation_cover T M P (syntaxCarrier V σ π d false)
    (syntaxCarrier V σ π d true) b p q rfl
  have hguard := (constantRepresentation_support T M P (syntaxCarrier V σ π d false)
    (syntaxCarrier V σ π d true) b p.val u q.val hu).2.1
  let x := ((F T M).map (prod.fst : P ⟶ V) p).val
  let t := ((F T M).map (prod.snd : P ⟶ _) p).val
  let φ := ConcreteNamedSubstitution.substitutionPayload V σ π d x t
  let v := ConcreteNamedSubstitution.mapChildren φ φ b u
  let k := ((b).withParameters P).eval.map (computedStatePair T V σ π d)
  let z := (F T M).map k.left q
  let left := (F T M).map (S).substitutionAlgebra.str.2.left z
  let source := (F T M).map (A₀).str.2.left q
  let right := (F T M).map (computedStatePair T V σ π d).2.left source
  have hz := computedState_polynomialCoordinates T V σ π d V M p b u q hu
  have hl := formulaSubstitution_structure_result_value T V σ π d M p v z hz
  have hlcode := (model_stateFormulaResultCode T P V σ π d M left).trans hl
  have hs := (constantLeaf_model T M P (syntaxCarrier V σ π d true) p
    (Coding.constructor true b u) source).mp (parameterFormula_coordinate T M P a b p u q hu)
  have hr := rawResultArrow_value T V V σ π d M true source
  erw [hs.1,hs.2] at hr
  have hrstate : ((F T M).map (stateResultCodeArrow T P V σ π d true) right).val =
      ConcreteNamedSubstitution.substitutionResult V σ π d x t (Coding.constructor true b u) := by
    change ((F T M).map (stateResultCodeArrow T P V σ π d true)
      ((F T M).map (computedStateFamily T V σ π d V true).left source)).val = _
    erw [← Functor.map_comp_apply,computedState_result]
    exact hr
  rw [ConcreteNamedSubstitution.substitutionResult,
    ConcreteNamedSubstitution.substitutionPayload_formula_constructor V σ π d x t u hguard] at hrstate
  have hresult : ((F T M).map (stateResultCodeArrow T P V σ π d true) left).val =
      ((F T M).map (stateResultCodeArrow T P V σ π d true) right).val := hlcode.trans hrstate.symm
  have horig := congrArg Prod.snd (computedStatePair_original_commutes T V σ π d)
  have he := congrArg Over.Hom.left horig
  change (k.left ≫ (S).substitutionAlgebra.str.2.left) ≫
      ((constantFamilyFunctor P).map (prod.fst : (S).substitutionCarriers.2 ⟶ (S).algebra.a.2)).left =
    ((A₀).str.2.left ≫ (computedStatePair T V σ π d).2.left) ≫
      ((constantFamilyFunctor P).map (prod.fst : (S).substitutionCarriers.2 ⟶ (S).algebra.a.2)).left at he
  have hold : (F T M).map
      ((constantFamilyFunctor P).map (prod.fst : (S).substitutionCarriers.2 ⟶ (S).algebra.a.2)).left left =
    (F T M).map
      ((constantFamilyFunctor P).map (prod.fst : (S).substitutionCarriers.2 ⟶ (S).algebra.a.2)).left right :=
    model_three_composition_equality T M k.left (S).substitutionAlgebra.str.2.left
      (A₀).str.2.left (computedStatePair T V σ π d).2.left
      ((constantFamilyFunctor P).map (prod.fst : (S).substitutionCarriers.2 ⟶ (S).algebra.a.2)).left he q
  apply model_statePoint_ext T M left right hold
  apply optionCode_injective T M (syntaxCarrier V σ π d true)
  exact ((model_stateFormulaResultCode T P V σ π d M left).symm.trans hresult).trans
    (model_stateFormulaResultCode T P V σ π d M right)

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
