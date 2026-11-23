/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalInseparability
public import Foundation.FirstOrder.LK.Basic
public import Mathlib.Computability.Reduce

/-! # Recursive reductions to theorem and refutation sets

Visser's Lemma 23, cited after Corollary 4.3, applies to every encoded
first-order language. A decider for the theorems of a consistent extension
would pull back along the reduction to a recursive separator.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.Entailment

namespace CategoricalEssentialIncompleteness.V46

/-- If a recursive sentence map sends two recursively inseparable sets to
the theorems and refutations of `T`, every consistent extension of `T` in
the same language has an undecidable set of theorem codes. -/
theorem essentiallyUndecidable_of_recursiveReduction {L : Language} [Encodable (Sentence L)]
    (T : Theory L) {P N : Set ℕ} (inseparable : Numerical.RecursivelyInseparable P N)
    (sentence : ℕ → Sentence L) (effective : Computable fun n ↦ Encodable.encode (sentence n))
    (positive : ∀ n ∈ P, T ⊢ sentence n) (negative : ∀ n ∈ N, T ⊢ ∼(sentence n))
    (U : Theory L) (extendsT : T ⪯ U) (consistent : Entailment.Consistent U) :
    ¬ ComputablePred (fun w : ℕ ↦ ∃ φ : Sentence L, Encodable.encode φ = w ∧ U ⊢ φ) := by
  intro decidableTheorems
  let D : Set ℕ := {n | U ⊢ sentence n}
  have decidablePreimage : ComputablePred (· ∈ D) := by
    apply ComputablePred.computable_of_manyOneReducible _ decidableTheorems
    refine ⟨_, effective, fun n ↦ ⟨fun h ↦ ⟨sentence n, rfl, h⟩, ?_⟩⟩
    rintro ⟨φ, sameCode, proof⟩
    change U ⊢ sentence n
    exact Encodable.encode_inj.mp sameCode ▸ proof
  apply inseparable.2
  refine ⟨D, decidablePreimage, fun n hn ↦ extendsT.wk (positive n hn), ?_⟩
  apply Set.disjoint_left.mpr
  intro n theoremOfU hn
  exact (consistent_iff_unprovable_bot.mp consistent)
    (neg_mdp (extendsT.wk (negative n hn)) (show U ⊢ sentence n from theoremOfU))

end CategoricalEssentialIncompleteness.V46
