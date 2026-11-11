/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonAdmissibleValues


/-! # Statement checks in `V46ConcreteNamedComparisonAdmissibleValuesChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.AdmissibleValuesChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local notation "S" => categoricalSyntax T V σ π d
local notation "P" => CategoricalSyntax.substitutionParameters (categoricalSyntax T V σ π d)
local notation "X" => (syntaxCarrier V σ π d false : PredicateCategory T)
local notation "Y" => (syntaxCarrier V σ π d true : PredicateCategory T)

example (a : Obj T M (S).admissibleSubstitution) :
    let q := (F T M).map (S).admissibleInclusion a
    ConcreteNamedSubstitution.substitutionResult V σ π d
      ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
      ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
      ((F T M).map prod.fst q).val =
        ConcreteNamedSubstitution.ok ((F T M).map (S).formulaSubstitution a).val :=
  canonical_formulaSubstitution_result T V σ π d M a
example (q : Obj T M (Y ⨯ P)) :
    (∃ a : Obj T M (S).admissibleSubstitution, (F T M).map (S).admissibleInclusion a = q) ↔
      ConcreteNamedSubstitution.substitutionFreeFor V σ π d
        ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
        ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
        ((F T M).map prod.fst q).val = 1 :=
  canonical_admissible_model_iff T V σ π d M q
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.AdmissibleValuesChecks
