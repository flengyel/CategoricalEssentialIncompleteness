/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Mathlib.Data.Nat.Basic

/-! # Independent sentences from a synthetic diagonal pair

Kirst and Peters, *Gödel's Theorem Without Tears*, Definitions 1, 3, 7, 17
and 18 and Theorem 20, use deterministic stage approximations as partial
functions. Their enumeration hypothesis (EPF) supplies an index for the
reversed proof search. The formal systems may have any type of sentences.
-/

@[expose] public section

set_option autoImplicit false

namespace CategoricalEssentialIncompleteness.V46.SyntheticComputability

universe u v

/-- A partial function in Kirst and Peters' Definition 3 returns at most
one value at each input across all stages. -/
structure PartialFunction (X : Type u) (Y : Type v) where
  run : X → ℕ → Option Y
  deterministic : ∀ x s t a b, run x s = some a → run x t = some b → a = b

def PartialFunction.Converges {X : Type u} {Y : Type v} (f : PartialFunction X Y)
    (x : X) (y : Y) : Prop := ∃ s, f.run x s = some y

/-- An enumeration satisfies the hypothesis EPF of Kirst and Peters, Axiom 13,
when every partial function has an index with the same graph. -/
def Enumerates (θ : ℕ → PartialFunction ℕ ℕ) : Prop :=
  ∀ f : PartialFunction ℕ ℕ, ∃ c, ∀ x y, (θ c).Converges x y ↔ f.Converges x y

/-- Definition 7 fixes the set of sentences, its negation operation, a
semidecision of provability and the exclusion of proofs of both signs. -/
structure FormalSystem (S : Type u) (neg : S → S) where
  provable : S → Prop
  semidecidable : ∃ test : S → ℕ → Bool, ∀ φ, provable φ ↔ ∃ s, test φ s = true
  consistent : ∀ φ, provable φ → provable (neg φ) → False

private def reverseSearch {S : Type u} (neg : S → S) (test : S → ℕ → Bool)
    (r : ℕ → S) (x s : ℕ) : Option ℕ :=
  if test (r x) s then some 0 else if test (neg (r x)) s then some 1 else none

private theorem reverseSearch_values {S : Type u} {neg : S → S} (U : FormalSystem S neg)
    (test : S → ℕ → Bool) (spec : ∀ φ, U.provable φ ↔ ∃ s, test φ s = true)
    (r : ℕ → S) (x y : ℕ) :
    (∃ s, reverseSearch neg test r x s = some y) ↔
      (U.provable (r x) ∧ y = 0) ∨ (U.provable (neg (r x)) ∧ y = 1) := by
  constructor
  · rintro ⟨s, h⟩
    cases hp : test (r x) s with
    | true =>
      exact Or.inl ⟨(spec _).mpr ⟨s, hp⟩, (by simpa [reverseSearch, hp] using h.symm)⟩
    | false =>
      cases hn : test (neg (r x)) s with
      | true =>
        exact Or.inr ⟨(spec _).mpr ⟨s, hn⟩, (by simpa [reverseSearch, hp, hn] using h.symm)⟩
      | false => simp [reverseSearch, hp, hn] at h
  · rintro (⟨p, rfl⟩ | ⟨n, rfl⟩)
    · obtain ⟨s, hs⟩ := (spec _).mp p
      exact ⟨s, by simp [reverseSearch, hs]⟩
    · obtain ⟨s, hs⟩ := (spec _).mp n
      have hp : test (r x) s = false := by
        cases h : test (r x) s with
        | false => rfl
        | true => exact (U.consistent _ ((spec _).mpr ⟨s, h⟩) n).elim
      exact ⟨s, by simp [reverseSearch, hp, hs]⟩

/-- A strong separation of the two diagonal outputs gives an independent
sentence in each consistent extension with semidecidable provability
(Kirst and Peters, Theorem 20, cited after Corollary 4.3). -/
theorem independent_in_extension {S : Type u} {neg : S → S}
    (θ : ℕ → PartialFunction ℕ ℕ) (epf : Enumerates θ)
    (T : FormalSystem S neg) (r : ℕ → S)
    (positive : ∀ x, (θ x).Converges x 1 → T.provable (r x))
    (negative : ∀ x, (θ x).Converges x 0 → T.provable (neg (r x)))
    (U : FormalSystem S neg) (extendsT : ∀ φ, T.provable φ → U.provable φ) :
    ∃ c, ¬ U.provable (r c) ∧ ¬ U.provable (neg (r c)) := by
  obtain ⟨test, spec⟩ := U.semidecidable
  have values := reverseSearch_values U test spec r
  let f : PartialFunction ℕ ℕ := {
    run := reverseSearch neg test r
    deterministic := by
      intro x s t a b hs ht
      rcases (values x a).mp ⟨s, hs⟩ with ⟨p, rfl⟩ | ⟨n, rfl⟩ <;>
        rcases (values x b).mp ⟨t, ht⟩ with ⟨p', rfl⟩ | ⟨n', rfl⟩
      · rfl
      · exact (U.consistent _ p n').elim
      · exact (U.consistent _ p' n).elim
      · rfl }
  obtain ⟨c, index⟩ := epf f
  refine ⟨c, ?_, ?_⟩
  · intro p
    have zero := (index c 0).mpr ((values c 0).mpr (Or.inl ⟨p, rfl⟩))
    exact U.consistent _ p (extendsT _ (negative c zero))
  · intro n
    have one := (index c 1).mpr ((values c 1).mpr (Or.inr ⟨n, rfl⟩))
    exact U.consistent _ (extendsT _ (positive c one)) n

end CategoricalEssentialIncompleteness.V46.SyntheticComputability
