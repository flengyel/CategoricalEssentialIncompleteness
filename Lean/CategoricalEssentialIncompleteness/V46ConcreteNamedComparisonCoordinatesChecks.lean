/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonCoordinates

/-! # The arbitrary arrow stays opaque in the actual product diagram -/
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

example (P A C X : PredicateCategory T) (f : P ⨯ C ⟶ X) (q : Obj T M (P ⨯ (A ⨯ C))) :
    (F T M).map (prod.snd : A ⨯ X ⟶ X)
      ((F T M).map (prod.snd : P ⨯ (A ⨯ X) ⟶ A ⨯ X) ((F T M).map (recursionLift T f) q)) =
        (F T M).map f ((F T M).map (prod.lift prod.fst
          (prod.snd ≫ prod.snd) : P ⨯ (A ⨯ C) ⟶ P ⨯ C) q) :=
  recursionLift_result T M f q
