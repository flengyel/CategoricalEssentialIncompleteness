/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainSubstitutionValues

/-! # Admissible-substitution points and the independent numeric free-for flag -/

@[expose] public section

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
local notation "S" => plainCategoricalSyntax T V σ π d
local notation "P" => CategoricalSyntax.substitutionParameters (plainCategoricalSyntax T V σ π d)
local notation "X" => (plainSyntaxCarrier V σ π d false : PredicateCategory T)
local notation "Y" => (plainSyntaxCarrier V σ π d true : PredicateCategory T)

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
/-- A point of the plain carrier has the same word in the canonical carrier, by the
inverse identity-graph morphism. -/
theorem plainPoint_canonical (formula : Bool)
    (word : Obj T M (plainSyntaxCarrier V σ π d formula)) :
    (syntaxCarrier V σ π d formula).val.Evalb ![word.val] := by
  have hw := ((F T M).map (syntaxPlainIso T V σ π d formula).inv word).property
  have hv := plainCarrierIso_inv_value T M formula
    (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d) word
  erw [hv] at hw
  exact hw

/-- This at-point equation needs no free-for premise. Its source is already a point of the
success pullback, and the real square identifies its successful output. -/
theorem plain_formulaSubstitution_result (a : Obj T M (S).admissibleSubstitution) :
    let q := (F T M).map (S).admissibleInclusion a
    ConcreteNamedSubstitution.substitutionResult V σ π d
      ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
      ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
      ((F T M).map prod.fst q).val =
        ConcreteNamedSubstitution.ok ((F T M).map (S).formulaSubstitution a).val := by
  let q := (F T M).map (S).admissibleInclusion a
  have hv := plain_formulaSubstitutionOption_value T V σ π d M q
  have hs : (F T M).map (S).formulaSubstitutionOption q =
      (F T M).map (coprod.inr (C := PredicateCategory T) («X» := ⊤_ (PredicateCategory T)) («Y» := Y)) ((F T M).map (S).formulaSubstitution a) := by
    exact parameterPoint_diagram T M (S).admissibleInclusion (S).formulaSubstitutionOption
      (S).formulaSubstitution (coprod.inr (C := PredicateCategory T) («X» := ⊤_ (PredicateCategory T)) («Y» := Y)) (S).formulaSubstitution_square a
  exact hv.symm.trans ((congrArg (optionCode T M Y) hs).trans
    (optionCode_inr T M Y ((F T M).map (S).formulaSubstitution a)))

theorem plain_formulaSubstitution_value (a : Obj T M (S).admissibleSubstitution) :
    let q := (F T M).map (S).admissibleInclusion a
    ((F T M).map (S).formulaSubstitution a).val =
      π₁ (ConcreteNamedSubstitution.substitutionResult V σ π d
        ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
        ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
        ((F T M).map prod.fst q).val) := by
  have h := congrArg (fun value : M => π₁ value) (plain_formulaSubstitution_result T V σ π d M a)
  simpa only [ConcreteNamedSubstitution.ok,pi₁_pair] using h.symm

/-- The flag is the separately defined and PA-verified raw free-for
recursion. Its equality with success is invoked as a proved theorem. -/
theorem plain_admissible_model_iff (q : Obj T M (Y ⨯ P)) :
    (∃ a : Obj T M (S).admissibleSubstitution, (F T M).map (S).admissibleInclusion a = q) ↔
      ConcreteNamedSubstitution.substitutionFreeFor V σ π d
        ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
        ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
        ((F T M).map prod.fst q).val = 1 := by
  change (∃ a : Obj T M (pullback (S).formulaSubstitutionOption (coprod.inr (C := PredicateCategory T) («X» := ⊤_ (PredicateCategory T)) («Y» := Y))),
      (F T M).map (pullback.fst (S).formulaSubstitutionOption (coprod.inr (C := PredicateCategory T) («X» := ⊤_ (PredicateCategory T)) («Y» := Y))) a = q) ↔ _
  refine (model_successFiber_iff T M (C := (Y ⨯ P)) (D := Y)
    (S).formulaSubstitutionOption q).trans ?_
  erw [plain_formulaSubstitutionOption_value T V σ π d M q]
  exact (ConcreteNamedSubstitution.substitutionFreeFor_iff_success V σ π d
    ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
    ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
    ((F T M).map prod.fst q).val
    (plainPoint_canonical T V σ π d M false
      ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)))
    (plainPoint_canonical T V σ π d M true
      ((F T M).map (prod.fst (C := PredicateCategory T) («X» := Y) («Y» := P)) q))).symm

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
