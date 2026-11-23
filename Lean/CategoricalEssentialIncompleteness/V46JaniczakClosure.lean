/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46JaniczakCoding
public import CategoricalEssentialIncompleteness.V46JaniczakTransfer

/-!
# Closing formulas over the finite set of variable names

The Gödel number bounds the variable names and the depth of the formula. Binding all names below this bound gives its universal closure.
-/

@[expose] public section

set_option autoImplicit false

namespace Janiczak.Formula

private theorem add_le_pair (a b : ℕ) : a+b ≤ Nat.pair a b := by
  simpa using Nat.unpair_add_le (Nat.pair a b)

theorem below_of_code_lt (p : Formula) (b : ℕ) (h : p.code < b) : Below b p := by
  induction p generalizing b with
  | equal x y =>
    change Nat.pair 0 (Nat.pair x y) < b at h
    have := add_le_pair x y; have := Nat.right_le_pair 0 (Nat.pair x y)
    exact ⟨by omega, by omega⟩
  | related x y =>
    change Nat.pair 1 (Nat.pair x y) < b at h
    have := add_le_pair x y; have := Nat.right_le_pair 1 (Nat.pair x y)
    exact ⟨by omega, by omega⟩
  | top => trivial
  | neg p ih => exact ih b ((Nat.right_le_pair 3 p.code).trans_lt h)
  | conj p q ih jh =>
    have l := (Nat.left_le_pair p.code q.code).trans (Nat.right_le_pair 4 _)
    have r := (Nat.right_le_pair p.code q.code).trans (Nat.right_le_pair 4 _)
    exact ⟨ih b (l.trans_lt h),jh b (r.trans_lt h)⟩
  | ex x p ih =>
    have l := (Nat.left_le_pair x p.code).trans (Nat.right_le_pair 5 _)
    have r := (Nat.right_le_pair x p.code).trans (Nat.right_le_pair 5 _)
    exact ⟨l.trans_lt h, ih b (r.trans_lt h)⟩

/-- The universal closure over all names below `b`. -/
def close (b : ℕ) (p : Formula) := neg (exBlock 0 p.neg b)

theorem below_close {b : ℕ} {p : Formula} (h : Below b p) : Below b (close b p) := by
  have hb (n : ℕ) (hn : n ≤ b) : Below b (exBlock 0 p.neg n) := by
    induction n with
    | zero => exact h
    | succ n ih => exact ⟨by omega, ih (by omega)⟩
  exact hb b le_rfl

theorem holds_congr_below {X : Type*} (E : X → X → Prop) {v w : ℕ → X} (p : Formula)
    {b : ℕ} (h : Below b p) (e : ∀ i < b, v i = w i) : p.Holds E v ↔ p.Holds E w := by
  induction p generalizing v w with
  | equal x y => simp only [Holds, e x h.1, e y h.2]
  | related x y => simp only [Holds, e x h.1, e y h.2]
  | top => rfl
  | neg p ih => exact not_congr (ih h e)
  | conj p q ih jh => exact and_congr (ih h.1 e) (jh h.2 e)
  | ex x p ih =>
    apply exists_congr
    intro a
    exact ih h.2 (fun i hi ↦ by
      by_cases he : i = x
      · simp [he]
      · simpa [Function.update_of_ne he] using e i hi)

theorem holds_close {X : Type*} (E : X → X → Prop) (v : ℕ → X) (p : Formula)
    {b : ℕ} (h : Below b p) :
    (close b p).Holds E v ↔ ∀ w, p.Holds E w := by
  classical
  simp only [close, Holds, holds_exBlock]
  constructor
  · intro hc u
    by_contra hu
    let w : ℕ → X := fun j ↦ if j < b then u j else v j
    refine hc ⟨w, ?_, ?_⟩
    · intro j hj
      have hn : ¬j < b := by omega
      simp [w,hn]
    · exact fun hw ↦ hu ((holds_congr_below E p h (fun i hi ↦ by simp [w,hi])).mp hw)
  · rintro ha ⟨w,-,hw⟩
    exact hw (ha w)

def closeCode (b e : ℕ) : ℕ :=
  Nat.pair 3 (Nat.rec (Nat.pair 3 e) (fun j v ↦ Nat.pair 5 (Nat.pair j v)) b)

theorem code_close (b : ℕ) (p : Formula) : (close b p).code = closeCode b p.code := by
  unfold close closeCode
  apply congrArg (Nat.pair 3)
  induction b with
  | zero => rfl
  | succ b ih =>
    change Nat.pair 5 (Nat.pair (0+b) _) = Nat.pair 5 (Nat.pair b _)
    rw [Nat.zero_add,ih]

theorem primrec_closeCode : Primrec₂ closeCode := by
  open Primrec in
  exact (to₂ <| Primrec₂.natPair.comp (const 3) (nat_rec' fst
    (Primrec₂.natPair.comp (const 3) snd) (to₂ <| Primrec₂.natPair.comp
      (const 5) (Primrec₂.natPair.comp (fst.comp snd) (snd.comp snd)))))

def depth : Formula → ℕ
  | equal .. | related .. | top => 1
  | neg p | ex _ p => p.depth + 1
  | conj p q => max p.depth q.depth + 1

theorem depth_pos (p : Formula) : 0 < p.depth := by cases p <;> simp [depth]

theorem depth_le_code (p : Formula) : p.depth ≤ p.code+1 := by
  induction p with
  | equal | related | top => exact Nat.succ_le_succ (Nat.zero_le _)
  | neg p ih => change p.depth+1 ≤ Nat.pair 3 p.code+1; have := add_le_pair 3 p.code; omega
  | ex x p ih =>
    change p.depth+1 ≤ Nat.pair 5 (Nat.pair x p.code)+1
    have := add_le_pair 5 (Nat.pair x p.code); have := Nat.right_le_pair x p.code; omega
  | conj p q ih jh =>
    change max p.depth q.depth+1 ≤ Nat.pair 4 (Nat.pair p.code q.code)+1
    have := add_le_pair 4 (Nat.pair p.code q.code); have := add_le_pair p.code q.code; omega

end Janiczak.Formula
