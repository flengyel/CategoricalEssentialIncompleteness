/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonCanonicalOperations
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonBooleans
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonSubstitutionComponents

/-! # The actual variable substitution branch has the numerical result -/

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
local instance namedComparisonVariableStepModelDecidableEq : DecidableEq M := Classical.decEq M
local notation "S" => categoricalSyntax T V σ π d
local notation "P" => CategoricalSyntax.substitutionParameters (categoricalSyntax T V σ π d)

theorem variableSubstitutionPair_result_value (q : Obj T M (P ⨯ V)) :
    ((F T M).map (prod.snd : (S).algebra.a.1 ⨯ (S).algebra.a.1 ⟶ _)
      ((F T M).map (S).variableSubstitutionPair q)).val =
    if ((F T M).map (prod.snd : P ⨯ V ⟶ V) q).val =
      ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.fst q)).val
    then ((F T M).map (prod.snd : P ⟶ _) ((F T M).map prod.fst q)).val
    else Coding.constructor false (SyntaxPolynomial.termExpression V σ d)
      (Arithmetic.pair ((F T M).map (prod.snd : P ⨯ V ⟶ V) q).val 0) := by
  let f := (prod.snd ≫ (S).variableConstructor : P ⨯ V ⟶ (S).algebra.a.1)
  let g := (prod.fst ≫ prod.snd : P ⨯ V ⟶ (S).algebra.a.1)
  let c := (prod.lift (prod.snd : P ⨯ V ⟶ V)
    (prod.fst ≫ prod.fst) : P ⨯ V ⟶ V ⨯ V)
  let χ := c ≫ SyntacticDecidableVariables.test T V
  have hv : (F T M).map (prod.snd : (S).algebra.a.1 ⨯ (S).algebra.a.1 ⟶ _)
      ((F T M).map (S).variableSubstitutionPair q) =
        (F T M).map (Two.branch χ f g) q := by
    exact model_lift_snd T M _ _ q
  have hg : ((F T M).map g q).val =
      ((F T M).map (prod.snd : P ⟶ _) ((F T M).map prod.fst q)).val := by
    rw [Functor.map_comp_apply]
    all_goals rfl
  have hf : ((F T M).map f q).val =
      Coding.constructor false (SyntaxPolynomial.termExpression V σ d)
        (Arithmetic.pair ((F T M).map (prod.snd : P ⨯ V ⟶ V) q).val 0) := by
    rw [Functor.map_comp_apply]
    exact CanonicalOperations.variable_value T M V σ π d _
  have hc₁ := model_lift_fst T M (prod.snd : P ⨯ V ⟶ V) (prod.fst ≫ prod.fst) q
  have hc₂ := model_lift_snd T M (prod.snd : P ⨯ V ⟶ V) (prod.fst ≫ prod.fst) q
  rw [congrArg Subtype.val hv]
  by_cases he : ((F T M).map (prod.snd : P ⨯ V ⟶ V) q).val =
      ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.fst q)).val
  · have hc := equalityTest_comp_point T M V c q true (by
      erw [hc₁,hc₂,Functor.map_comp_apply]
      exact iff_of_true he rfl)
    have hb := model_branch T M χ f g q true hc
    simpa only [↓reduceIte,he,hg] using congrArg Subtype.val hb
  · have hc := equalityTest_comp_point T M V c q false (by
      erw [hc₁,hc₂,Functor.map_comp_apply]
      exact iff_of_false he Bool.false_ne_true)
    have hb := model_branch T M χ f g q false hc
    simpa only [Bool.false_eq_true,↓reduceIte,he,hf] using congrArg Subtype.val hb

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
