/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSearch

/-! # Explicit functional-search statement correspondence -/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.ProofSearch FailureOfComposition.ConcreteEvaluator
open CategoricalEssentialIncompleteness.V46.SyntacticSearch

example (F : Graph) :
    ∃ e : ℕ, (𝗣𝗔 ⊢ soundSentence e F) ∧ (𝗣𝗔 ⊢ domainSentence e F) ∧
      ∀ (T : ArithmeticTheory) [𝗣𝗔 ⪯ T],
        (T ⊢ functionalSentence F) → Uniform T (eventualGraph e) F :=
  functional_search F

example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (F : Graph)
    (hF : T ⊢ functionalSentence F) :
    Uniform T (eventualGraph (searchIndex F)) F :=
  search_uniform_of_functional T F hF
