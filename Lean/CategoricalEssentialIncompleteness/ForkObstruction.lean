/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Card

/-! # The universal fork and the obstruction to natural decidable equality -/

@[expose] public section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.Fork

/-- The data of a set-valued functor on `1 ← 0 → 2`. -/
structure Diagram where
  center : Type
  left : Type
  right : Type
  leftMap : center → left
  rightMap : center → right

/-- The universal fork of Appendix A, with component carriers `ℕ⁴, ℕ², ℕ²`. -/
def universal : Diagram where
  center := ℕ × ℕ × ℕ × ℕ
  left := ℕ × ℕ
  right := ℕ × ℕ
  leftMap x := (x.1, x.2.2.1)
  rightMap x := (x.1, x.2.2.2)

/-- A natural map to the constant two-element diagram that decides equality
at every component. -/
structure EqualityDecision (X : Diagram) where
  center : X.center → X.center → Bool
  left : X.left → X.left → Bool
  right : X.right → X.right → Bool
  natural_left : ∀ x y, center x y = left (X.leftMap x) (X.leftMap y)
  natural_right : ∀ x y, center x y = right (X.rightMap x) (X.rightMap y)
  center_eq : ∀ x y, center x y = true ↔ x = y
  left_eq : ∀ x y, left x y = true ↔ x = y
  right_eq : ∀ x y, right x y = true ↔ x = y

theorem EqualityDecision.leftMap_injective {X : Diagram} (e : EqualityDecision X) :
    Function.Injective X.leftMap := by
  intro x y h
  apply (e.center_eq x y).mp
  rw [e.natural_left]
  exact (e.left_eq _ _).mpr h

/-- The component obstruction in Proposition B.10: no natural equality decision exists,
even among all set maps. -/
theorem universal_no_decidable_equality : ¬ Nonempty (EqualityDecision universal) := by
  rintro ⟨e⟩
  have h : (0, 0, 0, 0) = (0, 1, 0, 0) :=
    e.leftMap_injective (a₁ := (0, 0, 0, 0)) (a₂ := (0, 1, 0, 0)) rfl
  have he : (0 : ℕ) = 1 := congrArg (fun x : ℕ × ℕ × ℕ × ℕ => x.2.1) h
  exact Nat.zero_ne_one he

/-- The possible component supports of a subfunctor of the terminal fork. -/
def TerminalSupport :=
  {p : Bool × Bool × Bool // p.1 = true → p.2.1 = true ∧ p.2.2 = true}

instance : Fintype TerminalSupport := inferInstanceAs
  (Fintype {p : Bool × Bool × Bool // p.1 = true → p.2.1 = true ∧ p.2.2 = true})

theorem terminalSupport_card : Fintype.card TerminalSupport = 5 := by decide

end CategoricalEssentialIncompleteness.LocalConnectedness.Fork
