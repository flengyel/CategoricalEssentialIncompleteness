/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainSubstitutionComparison
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
local notation "S" => plainCategoricalSyntax T V σ π d
local notation "P" => CategoricalSyntax.substitutionParameters (plainCategoricalSyntax T V σ π d)
local notation "X" => (plainSyntaxCarrier V σ π d false : PredicateCategory T)
local notation "Y" => (plainSyntaxCarrier V σ π d true : PredicateCategory T)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem plain_termSubstitution_value (q : Obj T M (X ⨯ P)) :
    ((F T M).map (S).termSubstitution q).val =
      ConcreteNamedSubstitution.substitutionResult V σ π d
        ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
        ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
        ((F T M).map prod.fst q).val := by
  erw [plain_termSubstitution_eq_computed T V σ π d]
  exact braided_value T M (computedPlainTermResult T V V σ π d) Subtype.val
    (ConcreteNamedSubstitution.substitutionResult V σ π d)
    (fun z => computedPlainTermResult_value T V V σ π d M z) q

theorem plain_formulaSubstitutionOption_value (q : Obj T M (Y ⨯ P)) :
    optionCode T M Y ((F T M).map (S).formulaSubstitutionOption q) =
      ConcreteNamedSubstitution.substitutionResult V σ π d
        ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
        ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
        ((F T M).map prod.fst q).val := by
  erw [plain_formulaSubstitutionOption_eq_computed T V σ π d]
  apply braided_value T M (computedPlainFormulaResult T V V σ π d) (optionCode T M Y)
    (ConcreteNamedSubstitution.substitutionResult V σ π d) ?_ q
  intro z
  exact computedPlainFormulaResult_value T V V σ π d M z

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
