/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Finite.Basic

/-!
# Finitary inductive definitions

Appendix A cites Aczel's description of the least set closed under a set of rules
by finite proof sequences and proof trees (Propositions 1.1.4 and 1.4.5).
The premises of each rule form a finite set. Their cardinalities may be unbounded.
-/

@[expose] public section

set_option autoImplicit false

namespace CategoricalEssentialIncompleteness.V46.InductiveDefinition

universe u
variable {α : Type u}

/-- The rule \((P,x)\) allows the conclusion \(x\) from the premises in \(P\). -/
abbrev RuleSet (α : Type u) := Set (Set α × α)

def Closed (rules : RuleSet α) (S : Set α) : Prop :=
  ∀ {P : Set α} {x : α}, (P, x) ∈ rules → P ⊆ S → x ∈ S

def closure (rules : RuleSet α) : Set α :=
  {x | ∀ S : Set α, Closed rules S → x ∈ S}

def Finitary (rules : RuleSet α) : Prop :=
  ∀ {P : Set α} {x : α}, (P, x) ∈ rules → P.Finite

theorem closure_closed (rules : RuleSet α) : Closed rules (closure rules) :=
  fun h premises S closed => closed h fun _ member => premises member S closed

/-- The head of a proof sequence is its last conclusion. Each premise occurs in
the tail, among the conclusions already proved. -/
inductive ProofSequence (rules : RuleSet α) : List α → Prop
  | nil : ProofSequence rules []
  | cons {P : Set α} {x : α} {xs : List α} (rule : (P, x) ∈ rules)
      (previous : ProofSequence rules xs) (premises : ∀ p ∈ P, p ∈ xs) :
      ProofSequence rules (x :: xs)

private theorem ProofSequence.append {rules : RuleSet α} {xs ys : List α}
    (left : ProofSequence rules xs) (right : ProofSequence rules ys) :
    ProofSequence rules (xs ++ ys) := by
  induction left with
  | nil => exact right
  | cons rule _ premises ih =>
    exact .cons rule ih fun p hp => List.mem_append_left _ (premises p hp)

private theorem pack_sequences {rules : RuleSet α} {P : Set α} (finite : P.Finite)
    (proofs : ∀ p ∈ P, ∃ xs : List α, ProofSequence rules xs ∧ p ∈ xs) :
    ∃ xs : List α, ProofSequence rules xs ∧ ∀ p ∈ P, p ∈ xs := by
  classical
  induction P, finite using Set.Finite.induction_on with
  | empty => exact ⟨[], .nil, by simp⟩
  | @insert a S _ _ ih =>
    obtain ⟨first, firstProof, memFirst⟩ := proofs a (Set.mem_insert _ _)
    obtain ⟨rest, restProof, memRest⟩ := ih fun p hp => proofs p (Set.mem_insert_of_mem _ hp)
    refine ⟨first ++ rest, firstProof.append restProof, ?_⟩
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · exact List.mem_append_left _ memFirst
    · exact List.mem_append_right _ (memRest p hp)

/-- Aczel's finite sequences characterize the least rule-closed set. -/
theorem mem_closure_iff_sequence (rules : RuleSet α) (finite : Finitary rules) (x : α) :
    x ∈ closure rules ↔ ∃ earlier : List α, ProofSequence rules (x :: earlier) := by
  constructor
  · intro hx
    apply hx {p | ∃ earlier : List α, ProofSequence rules (p :: earlier)}
    intro P p rule children
    obtain ⟨xs, previous, premises⟩ := pack_sequences (finite rule) (fun z hz => by
      obtain ⟨earlier, proved⟩ := children hz
      exact ⟨z :: earlier, proved, List.mem_cons_self⟩)
    exact ⟨xs, .cons rule previous premises⟩
  · rintro ⟨earlier, proof⟩ S closed
    have sound : ∀ {xs : List α}, ProofSequence rules xs → ∀ p ∈ xs, p ∈ S := by
      intro xs pr
      induction pr with
      | nil => simp
      | cons rule _ premises ih =>
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact closed rule fun z hz => ih z (premises z hz)
        · exact ih p hp
    exact sound proof x List.mem_cons_self

/-- A node has one child for each of the entries of a finite enumeration of its
premise set. Leaves use rules with empty premise set. -/
inductive FiniteProofTree (rules : RuleSet α) : α → Type u
  | node {n : ℕ} {x : α} (premise : Fin n → α) (distinct : Function.Injective premise)
      (rule : (Set.range premise, x) ∈ rules)
      (child : (i : Fin n) → FiniteProofTree rules (premise i)) : FiniteProofTree rules x

/-- The conclusions of finite proof trees form precisely the least closed set. -/
theorem mem_closure_iff_finiteTree (rules : RuleSet α) (finite : Finitary rules) (x : α) :
    x ∈ closure rules ↔ Nonempty (FiniteProofTree rules x) := by
  classical
  constructor
  · intro hx
    apply hx {p | Nonempty (FiniteProofTree rules p)}
    intro P p rule children
    let := (finite rule).fintype
    let e := (Fintype.equivFin P).symm
    let premise : Fin (Fintype.card P) → α := fun i => (e i).val
    have range_eq : Set.range premise = P := by
      ext a
      constructor
      · rintro ⟨i, rfl⟩
        exact (e i).property
      · intro ha
        obtain ⟨i, hi⟩ := e.surjective ⟨a, ha⟩
        exact ⟨i, congrArg Subtype.val hi⟩
    have hr : (Set.range premise, p) ∈ rules := by rwa [range_eq]
    exact ⟨.node premise (Subtype.val_injective.comp e.injective) hr
      fun i => Classical.choice (children (e i).property)⟩
  · rintro ⟨tree⟩ S closed
    induction tree with
    | node premise _ rule _ ih =>
      apply closed rule
      rintro _ ⟨i, rfl⟩
      exact ih i

end CategoricalEssentialIncompleteness.V46.InductiveDefinition
