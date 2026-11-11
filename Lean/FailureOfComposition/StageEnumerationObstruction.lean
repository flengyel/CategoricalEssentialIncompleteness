/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Mathlib.Computability.Ackermann

/-!
# An enumeration without primitive-recursive stage bounds

A primitive-recursive stage test can enumerate every natural number while
admitting no primitive-recursive bound on its successful stages. Thus
extensional enumeration and primitive recursiveness of a stage test alone
do not imply effective stage selection. This counterexample does not identify
the stage test selected by `reTheoryStageWitness`.
-/

@[expose] public section

set_option autoImplicit false

namespace FailureOfComposition.StageEnumerationObstruction

open Nat.Partrec.Code

/-- Wait for a finite computation of the diagonal Ackermann value and require
the stage to be at least that value. All failures, including insufficient fuel,
return false. -/
def delayedStage (n s : ℕ) : Bool :=
  (evaln s (pappAck n) n).elim false (fun v => decide (v ≤ s))

theorem primrec_delayedStage : Primrec₂ delayedStage := by
  have he : Primrec (fun z : ℕ × ℕ => evaln z.2 (pappAck z.1) z.1) :=
    primrec_evaln.comp ((Primrec.snd.pair (primrec_pappAck.comp Primrec.fst)).pair Primrec.fst)
  have hl : Primrec (fun z : (ℕ × ℕ) × ℕ => decide (z.2 ≤ z.1.2)) :=
    (Primrec.nat_le.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).decide
  exact (Primrec.option_casesOn he (Primrec.const false) hl.to₂).of_eq (fun z => by
    unfold delayedStage
    cases evaln z.2 (pappAck z.1) z.1 <;> rfl)

/-- Every accepted stage dominates the corresponding diagonal Ackermann value. -/
theorem delayedStage_bound {n s : ℕ} (h : delayedStage n s = true) : ack n n ≤ s := by
  unfold delayedStage at h
  cases he : evaln s (pappAck n) n with
  | none => simp [he] at h
  | some v =>
      have hv : v ∈ (pappAck n).eval n := evaln_sound he
      have heq : v = ack n n := by simpa using hv
      simpa [he, heq] using h

theorem exists_delayedStage (n : ℕ) : ∃ s, delayedStage n s = true := by
  have hv : ack n n ∈ (pappAck n).eval n := by simp
  obtain ⟨s, hs⟩ := evaln_complete.mp hv
  refine ⟨max s (ack n n), ?_⟩
  have hm := evaln_mono (le_max_left s (ack n n)) hs
  change evaln (max s (ack n n)) (pappAck n) n = some (ack n n) at hm
  simp [delayedStage, hm]

/-- There is no primitive-recursive bound, even though every input has a
successful stage and the binary stage test is primitive recursive. -/
theorem no_primrec_stage_bound :
    ¬∃ bound : ℕ → ℕ, Primrec bound ∧ ∀ n, ∃ s ≤ bound n, delayedStage n s = true := by
  rintro ⟨bound, hpr, hb⟩
  obtain ⟨m, hm⟩ := exists_lt_ack_of_nat_primrec (Primrec.nat_iff.mp hpr)
  obtain ⟨s, hs, hw⟩ := hb m
  have hle := (delayedStage_bound hw).trans hs
  exact (not_lt_of_ge hle) (hm m)

/-- In particular, no primitive-recursive selector chooses successful stages. -/
theorem no_primrec_stage_selector :
    ¬∃ select : ℕ → ℕ, Primrec select ∧ ∀ n, delayedStage n (select n) = true := by
  rintro ⟨select, hpr, hs⟩
  exact no_primrec_stage_bound ⟨select, hpr, fun n => ⟨select n, le_rfl, hs n⟩⟩

end FailureOfComposition.StageEnumerationObstruction
