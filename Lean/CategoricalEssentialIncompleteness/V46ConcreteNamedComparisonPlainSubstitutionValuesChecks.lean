/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainSubstitutionValues


/-! # Categorical substitution outputs have the proved numeric graph values -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.PlainSubstitutionValuesChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local notation "S" => plainCategoricalSyntax T V σ π d
local notation "P" => CategoricalSyntax.substitutionParameters (plainCategoricalSyntax T V σ π d)
local notation "X" => (plainSyntaxCarrier V σ π d false : PredicateCategory T)
local notation "Y" => (plainSyntaxCarrier V σ π d true : PredicateCategory T)

example (q : Obj T M (X ⨯ P)) :
    ((F T M).map (S).termSubstitution q).val =
      ConcreteNamedSubstitution.substitutionResult V σ π d
        ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
        ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
        ((F T M).map prod.fst q).val :=
  plain_termSubstitution_value T V σ π d M q
example (q : Obj T M (Y ⨯ P)) :
    optionCode T M Y ((F T M).map (S).formulaSubstitutionOption q) =
      ConcreteNamedSubstitution.substitutionResult V σ π d
        ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
        ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
        ((F T M).map prod.fst q).val :=
  plain_formulaSubstitutionOption_value T V σ π d M q

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
example (q : Obj T M (X ⨯ P)) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    ((F T M).map (S).termSubstitution q).val =
      ConcreteNamedSubstitution.substitutionResult V σ π d
        ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
        ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
        ((F T M).map prod.fst q).val := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  exact plain_termSubstitution_value T V σ π d M q
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.PlainSubstitutionValuesChecks
