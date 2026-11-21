/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonGraphs

/-! # Restricted numerical occurrence morphisms have the algebra target -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

example (formula : Bool) :
    GraphMorphism T (syntaxCarrier V σ π d formula) (listObject T V) :=
  occurrencesMorphism T V σ π d formula

example : (SyntacticSyntax.categoricalSyntax T V σ π d).algebra.a ⟶
    (SyntacticSyntax.categoricalSyntax T V σ π d).occurrenceAlgebra.a :=
  occurrencesPair T V σ π d
