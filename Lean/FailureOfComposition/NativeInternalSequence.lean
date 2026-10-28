/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeInternalChecker

/-!
# Finite-set encoding of Boolean histories

`historyCode` encodes a Lean Boolean list as the internal finite set of its
index-bit pairs.  It is a comparison map into Foundation's HFS sequence
representation, separate from Lean's encodable list representation.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeInternalSequence

open FailureOfComposition.NativeInternalSyntax
open FailureOfComposition.NativeInternalChecker

/-- Encode the list by appending its numerical bits to an HFS sequence. -/
noncomputable def historyCode (xs : List Bool) : ℕ :=
  xs.foldl (fun s b => s ⁀' boolBit b) 0

@[simp] theorem historyCode_nil : historyCode [] = 0 := rfl

theorem historyCode_append (xs : List Bool) (b : Bool) :
    historyCode (xs ++ [b]) = historyCode xs ⁀' boolBit b := by
  simp [historyCode, List.foldl_append]

theorem historyCode_seq_length (xs : List Bool) :
    Seq (historyCode xs) ∧ lh (historyCode xs) = xs.length := by
  induction xs using List.reverseRecOn with
  | nil =>
      rw [historyCode_nil]
      simpa only [emptyset_def, List.length_nil] using
        (show Seq (∅ : ℕ) ∧ lh (∅ : ℕ) = 0 from ⟨seq_empty, lh_empty⟩)
  | append_singleton xs b ih =>
      rw [historyCode_append]
      exact ⟨ih.1.seqCons _, by simp [ih]⟩

set_option backward.isDefEq.respectTransparency false in
theorem historyCode_lookup (xs : List Bool) (i : ℕ) :
    znth (historyCode xs) i = boolBit (xs.getD i false) := by
  induction xs using List.reverseRecOn with
  | nil =>
      rw [historyCode_nil, znth_prop_not (Or.inr (by
        rw [← emptyset_def, lh_empty]
        change (0 : ℕ) = i ∨ 0 < i
        omega))]
      simp
  | append_singleton xs b ih =>
      have hs := (historyCode_seq_length xs).1
      have hl := (historyCode_seq_length xs).2
      rw [historyCode_append]
      by_cases hi : i < xs.length
      · rw [List.getD_append _ _ _ _ hi, ← ih]
        exact (hs.seqCons _).znth_eq_of_mem
          (Seq.mem_seqCons_iff_of_lt (by simpa [hl] using hi) |>.mpr
            (hs.znth (by simpa [hl] using hi)))
      · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hi)]
        by_cases he : i = xs.length
        · subst i
          simpa [hl] using (hs.seqCons (boolBit b)).znth_eq_of_mem
            (lh_mem_seqCons (historyCode xs) (boolBit b))
        · rw [znth_prop_not (Or.inr (by
            rw [hs.lh_seqCons, hl]
            exact succ_le_iff_lt.mpr
              (Nat.lt_of_le_of_ne (Nat.le_of_not_gt hi) (Ne.symm he))))]
          have hsub : 1 ≤ i - xs.length := by omega
          rw [List.getD_eq_default [b] false hsub]
          rfl

theorem historyCode_accepts_iff (xs : List Bool) (i : ℕ) :
    historyAccept (historyCode xs) i ↔ xs.getD i false = true := by
  rw [historyAccept, historyCode_lookup]
  cases xs.getD i false <;> simp

end FailureOfComposition.NativeInternalSequence
