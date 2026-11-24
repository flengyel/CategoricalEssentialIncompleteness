/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FinitaryInductiveDefinitions

/-! # The two finite characterizations of inductive generation in Appendix A.5 -/

@[expose] public section

set_option autoImplicit false

namespace CategoricalEssentialIncompleteness.V46.InductiveDefinition.Checks

universe u

theorem least_closed_iff_finite_proofs {α : Type u} (rules : Set (Set α × α))
    (finite : ∀ (P : Set α) (c : α), (P, c) ∈ rules → P.Finite) (x : α) :
    let generated := ∀ S : Set α,
      (∀ (P : Set α) (c : α), (P, c) ∈ rules → P ⊆ S → c ∈ S) → x ∈ S
    (generated ↔ ∃ earlier : List α, ProofSequence rules (x :: earlier)) ∧
      (generated ↔ Nonempty (FiniteProofTree rules x)) := by
  have fin : Finitary rules := fun {P c} h => finite P c h
  have generated : (∀ S : Set α,
      (∀ (P : Set α) (c : α), (P, c) ∈ rules → P ⊆ S → c ∈ S) → x ∈ S) ↔
      x ∈ closure rules :=
    ⟨fun h S closed => h S fun _ _ r prem => closed r prem,
      fun h S closed => h S fun {P c} r prem => closed P c r prem⟩
  exact ⟨generated.trans (mem_closure_iff_sequence rules fin x),
    generated.trans (mem_closure_iff_finiteTree rules fin x)⟩

end CategoricalEssentialIncompleteness.V46.InductiveDefinition.Checks

open CategoricalEssentialIncompleteness.V46.InductiveDefinition

#print axioms mem_closure_iff_sequence
#print axioms mem_closure_iff_finiteTree
#print axioms Checks.least_closed_iff_finite_proofs
