/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakSignedTheory

/-! # The numerical passage on the signed equivalence-relation theory

The first statement expands essential undecidability using Foundation sentences,
ordinary Gödel codes and native first-order derivability. The second fixes the
positive and negative class-size witnesses on the concrete model.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder

namespace Janiczak.SignedTheoryChecks

theorem native_proof_words {P N : Set ℕ} (hd : Disjoint P N) :
    (∀ U : Theory FOL.L, FOL.theory (Signed P N) ⊆ U → Entailment.Consistent U →
      ¬ ComputablePred (fun w : ℕ ↦ ∃ φ : Sentence FOL.L, Encodable.encode φ = w ∧ U ⊢ φ)) ↔
    (Disjoint P N ∧ ¬ ∃ C : Set ℕ, ComputablePred (· ∈ C) ∧ P ⊆ C ∧ Disjoint C N) :=
  FOL.signed_essentiallyUndecidable_iff hd

theorem class_index (C : Set ℕ) (n : ℕ) :
    (canonical C).Valid (Formula.sizeSentence n) ↔ n ∈ C := by
  obtain ⟨v⟩ := (canonical C).hasValuation
  exact ⟨fun h ↦ (Canonical.spectrum n).mp ((Formula.holds_sizeSentence _ _ n).mp (h v)),
    fun hc _ ↦ (Formula.holds_sizeSentence _ _ n).mpr ((Canonical.spectrum n).mpr hc)⟩

theorem recursive_axioms {P N : Set ℕ} (hp : REPred (· ∈ P)) (hn : REPred (· ∈ N)) :
    ∃ U : Theory FOL.L, PrimrecPred (fun w : ℕ ↦ w ∈ Encodable.encode '' U) ∧
      ∀ φ : Sentence FOL.L, (U ⊢ φ ↔ FOL.theory (Signed P N) ⊢ φ) :=
  FOL.signed_recursively_axiomatizable hp hn

end Janiczak.SignedTheoryChecks

#print axioms Janiczak.SignedTheoryChecks.native_proof_words
#print axioms Janiczak.SignedTheoryChecks.class_index
#print axioms Janiczak.SignedTheoryChecks.recursive_axioms
