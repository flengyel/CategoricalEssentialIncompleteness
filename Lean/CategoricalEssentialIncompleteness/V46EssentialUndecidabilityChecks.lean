/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46EssentialUndecidability

/-! # The extension quantifier in Visser's Lemma 23 -/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder

namespace CategoricalEssentialIncompleteness.V46.EssentialUndecidabilityChecks

theorem every_consistent_extension {L : Language} [Encodable (Sentence L)]
    {T : Theory L} {P N : Set ℕ} (pair : Numerical.RecursivelyInseparable P N)
    (f : ℕ → Sentence L) (hf : Computable fun n ↦ Encodable.encode (f n))
    (hp : ∀ n ∈ P, T ⊢ f n) (hn : ∀ n ∈ N, T ⊢ ∼(f n)) :
    ∀ U : Theory L, T ⊆ U → Entailment.Consistent U →
      ¬ ComputablePred (fun w : ℕ ↦ ∃ φ : Sentence L, w = Encodable.encode φ ∧ U ⊢ φ) := by
  intro U inclusion consistent decider
  apply essentiallyUndecidable_of_recursiveReduction T pair f hf hp hn U
    (Theory.Proof.weakerThan_of_le inclusion) consistent
  exact decider.of_eq fun w ↦ by simp only [eq_comm (a := w)]

end CategoricalEssentialIncompleteness.V46.EssentialUndecidabilityChecks

open CategoricalEssentialIncompleteness.V46

#print axioms essentiallyUndecidable_of_recursiveReduction
#print axioms EssentialUndecidabilityChecks.every_consistent_extension
