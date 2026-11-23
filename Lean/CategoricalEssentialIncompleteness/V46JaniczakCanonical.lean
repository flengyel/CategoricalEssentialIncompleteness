/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakModels
public import CategoricalEssentialIncompleteness.V46JaniczakTheories

/-!
# Models with a prescribed finite class spectrum

There is one class of size $i+1$ for every selected index $i$ and a countable family of countably infinite classes. This model witnesses the consistency of every disjoint signing.
-/

@[expose] public section

set_option autoImplicit false

namespace Janiczak

/-- There is one finite class of size `i+1` for each selected `i`, and one
countably infinite class for each natural number. -/
def Fiber (C : Set ℕ) : C ⊕ ℕ → Type
  | .inl i => Fin (i.val+1)
  | .inr _ => ℕ

def canonical (C : Set ℕ) : Structure where
  Carrier := (t : C ⊕ ℕ) × Fiber C t
  inhabited := ⟨⟨.inr 0, (0 : ℕ)⟩⟩
  rel x y := x.1 = y.1

namespace Canonical

variable {C : Set ℕ}

def classEquiv (x : (canonical C).Carrier) :
    Fiber C x.1 ≃ {y : (canonical C).Carrier // (canonical C).rel x y} where
  toFun t := ⟨⟨x.1, t⟩, rfl⟩
  invFun y := y.property.symm ▸ y.val.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨k, j⟩, h⟩
    change x.1 = k at h
    subst k
    rfl

theorem sized_iff (x : (canonical C).Carrier) (n : ℕ) :
    Sized (canonical C).rel x n ↔ ∃ i : C, x.1 = .inl i ∧ n = i.val+1 := by
  rcases x with ⟨k, p⟩
  let e := classEquiv (C := C) ⟨k, p⟩
  constructor
  · rintro ⟨f⟩
    have g := f.trans e.symm
    cases k with
    | inl i => exact ⟨i, rfl, by simpa [Fiber] using Fintype.card_congr (show Fin n ≃ Fin (i.val+1) from g)⟩
    | inr k =>
      have : Finite ℕ := Finite.of_equiv (Fin n) g
      exact (not_finite ℕ).elim
  · rintro ⟨i, hk, rfl⟩
    cases hk
    exact ⟨e⟩

theorem spectrum (i : ℕ) : (∃ x, Sized (canonical C).rel x (i+1)) ↔ i ∈ C := by
  constructor
  · rintro ⟨x, h⟩
    obtain ⟨j, -, hj⟩ := (sized_iff x _).mp h
    exact Nat.succ_inj.mp hj ▸ j.property
  · intro hi
    let t : C := ⟨i, hi⟩
    exact ⟨⟨.inl t, (0 : Fin (i+1))⟩, (sized_iff _ _).mpr ⟨t, rfl, rfl⟩⟩

theorem models_jan : (canonical C).Models Jan := by
  intro p hp v
  cases hp with
  | refl =>
    rw [Formula.reflSentence, Formula.holds_all]
    exact fun _ ↦ rfl
  | symm =>
    simp only [Formula.symmSentence, Formula.holds_all, Formula.holds_imp, Formula.Holds]
    simp [canonical, eq_comm]
  | trans =>
    simp only [Formula.transSentence, Formula.holds_all, Formula.holds_imp, Formula.Holds]
    simp [canonical]
    exact fun _ _ _ ↦ Eq.trans
  | uniqueSize n =>
    rw [Formula.holds_uniqueSize]
    intro a b ha hb
    obtain ⟨i, hi, hn⟩ := (sized_iff a n).mp ha
    obtain ⟨j, hj, hnj⟩ := (sized_iff b n).mp hb
    have e : i = j := Subtype.ext (by omega)
    exact hi.trans ((congrArg Sum.inl e).trans hj.symm)
  | manyLarge n =>
    rw [Formula.holds_manyLarge]
    let f : Fin n → (canonical C).Carrier := fun i ↦ ⟨.inr i.val, (0 : ℕ)⟩
    refine ⟨f, fun i j h ↦ ?_, fun i ↦ ?_⟩
    · change ¬ (Sum.inr i.val : C ⊕ ℕ) = Sum.inr j.val
      simpa using (Nat.ne_of_lt (show i.val < j.val from h))
    · let g : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
      exact ⟨g.trans (classEquiv (f i)).toEmbedding⟩

theorem models_signed {P N : Set ℕ} (hp : P ⊆ C) (hn : Disjoint C N) :
    (canonical C).Models (Signed P N) := by
  intro p h v
  cases h with
  | jan h => exact models_jan _ h v
  | pos h => exact (Formula.holds_sizeSentence _ _ _).mpr (spectrum _ |>.mpr (hp h))
  | neg h =>
    exact fun ha ↦ Set.disjoint_left.mp hn (spectrum _ |>.mp
      ((Formula.holds_sizeSentence _ _ _).mp ha)) h

theorem consistent_signed {P N : Set ℕ} (h : Disjoint P N) : Consistent (Signed P N) :=
  ⟨canonical P, models_signed (fun _ h ↦ h) h⟩

end Canonical
end Janiczak
