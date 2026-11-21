/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonSentences

/-! # The sentence image is the positive formula-and-empty-FV predicate -/

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
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

example : T ⊢ sentenceCarrierLiteralSentence T V σ π d :=
  sentenceCarrier_literal_theory T V σ π d

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (word : M) :
    (SyntacticSentenceImages.sentenceCarrier T
      (plainCategoricalSyntax T V σ π d).sentenceInclusion).val.Evalb ![word] ↔
        (literalSentenceCarrier T V σ π d).val.Evalb ![word] :=
  sentenceCarrier_literal T V σ π d M word
