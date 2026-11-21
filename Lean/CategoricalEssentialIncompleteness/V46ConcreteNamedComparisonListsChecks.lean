/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonLists

/-! # Stable-list initiality identifies numerical concatenation -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (V : PredicateCategory T)

example : appendParameterArrow T V = (lists T V).appendParameterValue := appendParameter_eq T V

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q : Obj T M (listObject T V ⨯ listObject T V)) :
    ((F T M).map (lists T V).append q).val =
      CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Words.append
        ((F T M).map (prod.fst : listObject T V ⨯ listObject T V ⟶ listObject T V) q).val
        ((F T M).map (prod.snd : listObject T V ⨯ listObject T V ⟶ listObject T V) q).val :=
  append_value T V M q
