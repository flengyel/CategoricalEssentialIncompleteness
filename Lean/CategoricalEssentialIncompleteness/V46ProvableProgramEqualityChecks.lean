/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ProvableProgramEquality

/-! # Ordinary totalization modulo PA-provable graph equality in §8.6 -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.ConcreteEvaluator FailureOfComposition.ProofSearch

namespace CategoricalEssentialIncompleteness.V46.ProvableProgramEquality.Checks

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (e : ℕ) (n x y : M) :
    (applicationGraph e).val.Evalb ![ExponentialPairing.code n x, y] ↔
      ∃ j : M, UniformTrace.graph.val.Evalb ![(e : M), n, j] ∧
        UniformTrace.graph.val.Evalb ![j, x, y] := applicationGraph_pair e n x y

example {e n j : ℕ} (h : j ∈ Kleene.eval e n) :
    𝗣𝗔 ⊢ uniformSentence (eventualGraph (totalizer e n)) (eventualGraph j) := totalizer_eqIndex h

example (f : ℕ →. ℕ) (hf : Partrec f) :
    ∃ g : ℕ → ℕ, Computable g ∧ ∀ n j : ℕ, j ∈ f n →
      𝗣𝗔 ⊢ uniformSentence (eventualGraph j) (eventualGraph (g n)) := uniform_totalization f hf

end CategoricalEssentialIncompleteness.V46.ProvableProgramEquality.Checks
