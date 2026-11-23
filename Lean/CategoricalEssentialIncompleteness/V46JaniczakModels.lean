/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakLanguage

/-!
# Truth of the finite class-size sentences

An injection from a finite ordinal expresses a lower bound on class size. A bijection expresses exact size. These characterizations interpret the two axiom schemas in Janiczak’s theory.
-/

@[expose] public section

set_option autoImplicit false

namespace Janiczak
open Formula

/-- An injection from `Fin n` enumerates `n` distinct members of the class of `x`. -/
def Large {X : Type*} (E : X → X → Prop) (x : X) (n : ℕ) :=
  Nonempty (Fin n ↪ {y // E x y})

/-- A bijection from `Fin n` enumerates the entire class of `x`. -/
def Sized {X : Type*} (E : X → X → Prop) (x : X) (n : ℕ) :=
  Nonempty (Fin n ≃ {y // E x y})

namespace Formula

variable {X : Type*} (E : X → X → Prop) (v : ℕ → X)

theorem holds_distinctBelow (n : ℕ) :
    (distinctBelow n).Holds E v ↔ Function.Injective (fun j : Fin n ↦ v j) := by
  simp only [distinctBelow, holds_conjBelow, Holds]
  constructor
  · intro h i j he
    apply Fin.ext
    by_contra hn
    rcases lt_or_gt_of_ne hn with hl | hl
    · exact h j j.isLt i hl he
    · exact h i i.isLt j hl he.symm
  · intro h j hj i hij he
    have eq : (⟨i, by omega⟩ : Fin n) = ⟨j, hj⟩ := h he
    exact (Nat.ne_of_lt hij) (congrArg Fin.val eq)

private def replaceBlock (a n : ℕ) (f : Fin n → X) (v : ℕ → X) (j : ℕ) :=
  if h : a ≤ j ∧ j < a+n then f ⟨j-a, by omega⟩ else v j

private theorem replaceBlock_out (a n : ℕ) (f : Fin n → X) (v : ℕ → X) {j : ℕ}
    (h : j < a ∨ a+n ≤ j) : replaceBlock a n f v j = v j := by
  simp [replaceBlock, show ¬(a ≤ j ∧ j < a+n) by omega]

private theorem replaceBlock_in (a n : ℕ) (f : Fin n → X) (v : ℕ → X)
    (i : Fin n) : replaceBlock a n f v (a+i) = f i := by
  have : a ≤ a+(i : ℕ) ∧ a+(i : ℕ) < a+n := by have := i.isLt; omega
  simp [replaceBlock, this]

theorem holds_atLeast (n x : ℕ) (hx : n ≤ x) :
    (atLeast n x).Holds E v ↔ Large E (v x) n := by
  rw [atLeast, holds_exBlock]
  simp only [Holds, holds_distinctBelow, holds_conjBelow]
  constructor
  · rintro ⟨w, he, h, hw⟩
    have wx : w x = v x := he x (by omega)
    exact ⟨⟨fun i ↦ ⟨w i, wx ▸ hw i i.isLt⟩, fun _ _ hi ↦ h (congrArg Subtype.val hi)⟩⟩
  · rintro ⟨f⟩
    let w := replaceBlock 0 n (fun i ↦ (f i).val) v
    have wi (i : Fin n) : w i = (f i).val := by
      simpa [w] using replaceBlock_in 0 n (fun i ↦ (f i).val) v i
    have wx : w x = v x := replaceBlock_out 0 n _ _ (by omega)
    refine ⟨w, fun _ h ↦ replaceBlock_out _ _ _ _ h, ?_, ?_⟩
    · exact fun i j h ↦ f.injective (Subtype.ext ((wi i).symm.trans (h.trans (wi j))))
    · intro i hi
      rw [wx, wi ⟨i, hi⟩]
      exact (f ⟨i, hi⟩).property

theorem holds_exactly (n x : ℕ) (hx : n < x) :
    (exactly n x).Holds E v ↔ Sized E (v x) n := by
  rw [exactly, holds_exBlock]
  simp only [Holds, holds_distinctBelow, holds_conjBelow, holds_all, holds_imp,
    holds_disjBelow, Function.update_self, Function.update_of_ne (Nat.ne_of_gt hx)]
  constructor
  · rintro ⟨w, he, h, hw, ha⟩
    have wx : w x = v x := he x (by omega)
    let f : Fin n → {y // E (v x) y} := fun i ↦ ⟨w i, wx ▸ hw i i.isLt⟩
    refine ⟨Equiv.ofBijective f ⟨fun _ _ hi ↦ h (congrArg Subtype.val hi), ?_⟩⟩
    intro y
    obtain ⟨i, hi, hh⟩ := ha y.val (wx.symm ▸ y.property)
    rw [Function.update_of_ne (Nat.ne_of_lt hi)] at hh
    exact ⟨⟨i,hi⟩, Subtype.ext hh.symm⟩
  · rintro ⟨f⟩
    let w := replaceBlock 0 n (fun i ↦ (f i).val) v
    have wi (i : Fin n) : w i = (f i).val := by
      simpa [w] using replaceBlock_in 0 n (fun i ↦ (f i).val) v i
    have wx : w x = v x := replaceBlock_out 0 n _ _ (by omega)
    refine ⟨w, fun _ h ↦ replaceBlock_out _ _ _ _ h, ?_, ?_, ?_⟩
    · exact fun i j h ↦ f.injective (Subtype.ext ((wi i).symm.trans (h.trans (wi j))))
    · intro i hi
      rw [wx, wi ⟨i, hi⟩]
      exact (f ⟨i, hi⟩).property
    · intro a ha
      obtain ⟨i, hi⟩ := f.surjective ⟨a, wx ▸ ha⟩
      refine ⟨i, i.isLt, ?_⟩
      rw [Function.update_of_ne (Nat.ne_of_lt i.isLt), wi i]
      exact (congrArg Subtype.val hi).symm

@[simp] theorem holds_sizeSentence (i : ℕ) :
    (sizeSentence i).Holds E v ↔ ∃ a, Sized E a (i+1) := by
  simp only [sizeSentence, Holds, holds_exactly _ _ (i+1) (i+2) (by omega), Function.update_self]

@[simp] theorem holds_uniqueSize (n : ℕ) :
    (uniqueSize n).Holds E v ↔ ∀ a b, Sized E a n → Sized E b n → E a b := by
  simp only [uniqueSize, holds_all, holds_imp, Holds, holds_exactly _ _ n (n+1) (by omega),
    holds_exactly _ _ n (n+2) (by omega), Function.update_of_ne (show n+1 ≠ n+2 by omega), Function.update_self, and_imp]

theorem holds_manyLarge (n : ℕ) :
    (manyLarge n).Holds E v ↔ ∃ f : Fin n → X,
      (∀ i j, i < j → ¬ E (f i) (f j)) ∧ ∀ i, Large E (f i) n := by
  rw [manyLarge, holds_exBlock]
  simp only [Holds, holds_conjBelow]
  have hl (w : ℕ → X) (i : ℕ) := holds_atLeast E w n (n+1+i) (by omega)
  simp only [hl]
  constructor
  · rintro ⟨w, -, h, h'⟩
    exact ⟨fun i ↦ w (n+1+i), fun i j hj ↦ h j j.isLt i hj,
      fun i ↦ h' i i.isLt⟩
  · rintro ⟨f, h, h'⟩
    let w := replaceBlock (n+1) n f v
    have wi (i : Fin n) : w (n+1+i) = f i := replaceBlock_in _ _ _ _ i
    refine ⟨w, fun _ ho ↦ replaceBlock_out _ _ _ _ ho, ?_, ?_⟩
    · intro j hj i hi
      rw [wi ⟨i, by omega⟩, wi ⟨j, hj⟩]
      exact h _ _ hi
    · intro i hi
      rw [wi ⟨i, hi⟩]
      exact h' _

end Formula

end Janiczak
