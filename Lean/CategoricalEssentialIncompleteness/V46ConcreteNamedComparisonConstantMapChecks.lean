/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonConstantMap

/-! # A forward fixed-fiber chart lemma uses actual over-parameter arrows -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

example (P C : PredicateCategory T) (p : Obj T M P) (u : M) (z : Obj T M (P ⨯ C)) :
    (constantLeaf T P C).val.Evalb ![p.val,u,z.val] ↔
      (F T M).map (prod.fst : P ⨯ C ⟶ P) z = p ∧
        ((F T M).map (prod.snd : P ⨯ C ⟶ C) z).val = u :=
  constantLeaf_model T M P C p u z
