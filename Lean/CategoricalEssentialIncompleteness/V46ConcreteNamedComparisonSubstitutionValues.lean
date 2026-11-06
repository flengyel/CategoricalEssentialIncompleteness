/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonSubstitutionHom
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonBraidedValues

/-! # Actual categorical substitution outputs have the proved numeric graph values -/

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
local notation "S" => categoricalSyntax T V σ π d
local notation "P" => CategoricalSyntax.substitutionParameters (categoricalSyntax T V σ π d)
local notation "X" => (syntaxCarrier V σ π d false : PredicateCategory T)
local notation "Y" => (syntaxCarrier V σ π d true : PredicateCategory T)

theorem canonical_termSubstitution_eq_computed :
    (S).termSubstitution = (prod.braiding (C := PredicateCategory T) X P).hom ≫ computedTermResult T V V σ π d := by
  change (prod.braiding (C := PredicateCategory T) X P).hom ≫ (S).substitutionFold.1.left ≫ prod.snd ≫ prod.snd = _
  erw [← computedStatePair_eq_fold T V σ π d,computedState_result T V σ π d V false]
  dsimp only [computedTermResult]

theorem canonical_formulaSubstitutionOption_eq_computed :
    (S).formulaSubstitutionOption = (prod.braiding (C := PredicateCategory T) Y P).hom ≫ computedFormulaResult T V V σ π d := by
  change (prod.braiding (C := PredicateCategory T) Y P).hom ≫ (S).substitutionFold.2.left ≫ prod.snd ≫ prod.snd = _
  erw [← computedStatePair_eq_fold T V σ π d]
  congr 1
  change (computedFormulaState T V V σ π d).left ≫ prod.snd ≫ prod.snd = _
  dsimp only [computedFormulaState,Over.homMk_left]
  erw [prod.lift_snd_assoc,prod.lift_snd]

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem canonical_termSubstitution_value (q : Obj T M (X ⨯ P)) :
    ((F T M).map (S).termSubstitution q).val =
      ConcreteNamedSubstitution.substitutionResult V σ π d
        ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
        ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
        ((F T M).map prod.fst q).val := by
  erw [canonical_termSubstitution_eq_computed T V σ π d]
  exact braided_value T M (computedTermResult T V V σ π d) Subtype.val
    (ConcreteNamedSubstitution.substitutionResult V σ π d)
    (fun z => rawResultArrow_value T V V σ π d M false z) q

theorem canonical_formulaSubstitutionOption_value (q : Obj T M (Y ⨯ P)) :
    optionCode T M Y ((F T M).map (S).formulaSubstitutionOption q) =
      ConcreteNamedSubstitution.substitutionResult V σ π d
        ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
        ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
        ((F T M).map prod.fst q).val := by
  erw [canonical_formulaSubstitutionOption_eq_computed T V σ π d]
  apply braided_value T M (computedFormulaResult T V V σ π d) (optionCode T M Y)
    (ConcreteNamedSubstitution.substitutionResult V σ π d) ?_ q
  intro z
  exact (computedFormulaResult_code T V V σ π d M z).trans
    (rawResultArrow_value T V V σ π d M true z)

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
