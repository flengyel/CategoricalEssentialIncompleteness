/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonOccurrences

/-! # The numerical free-variable candidates form an actual algebra Hom -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

example : (categoricalSyntax T V σ π d).algebra ⟶
    (categoricalSyntax T V σ π d).occurrenceAlgebra := occurrenceHom T V σ π d

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (word : Obj T M ((categoricalSyntax T V σ π d).algebra.a.2)) :
    ((F T M).map (categoricalSyntax T V σ π d).formulaOccurrences word).val =
      ConcreteNamedSubstitution.freeVariables V σ π d word.val :=
  formulaOccurrences_value T V σ π d M word

example (V₀ : PredicateCategory 𝗣𝗔) (σ₀ π₀ : ℕ → PredicateCategory 𝗣𝗔) (d₀ : ℕ) :
    𝗣𝗔 ⊢ uniformSentence
      (chosenGraph 𝗣𝗔 (categoricalSyntax 𝗣𝗔 V₀ σ₀ π₀ d₀).formulaOccurrences).graph
      (occurrencesGraph V₀ σ₀ π₀ d₀ true) :=
  formulaOccurrences_graph_theory 𝗣𝗔 V₀ σ₀ π₀ d₀
