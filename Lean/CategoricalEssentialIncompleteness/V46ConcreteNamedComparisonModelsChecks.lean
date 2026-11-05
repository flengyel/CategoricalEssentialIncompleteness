/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonModels

/-! # Model evaluation of actual finite categorical conditionals -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open CategoricalEssentialIncompleteness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

example {X Y : PredicateCategory T} (χ : X ⟶ Two (PredicateCategory T))
    (f g : X ⟶ Y) (x : Obj T M X) (b : Bool)
    (hb : (F T M).map χ x = (F T M).map (Two.constant X b) x) :
    (F T M).map (Two.branch χ f g) x = (F T M).map (if b then g else f) x :=
  model_branch T M χ f g x b hb
