/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxTrace

/-! # Concatenating actual forward computation records -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
open Coding
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Concatenation retains the first record's final state once and
appends the second record's remaining states by the actual arithmetic
whole-vector append. It neither chooses an external list nor drops any
positive operation witness. -/
theorem traceRecord_concat {p word suffix initial states other : M}
    (h : A.TraceRecord p word initial (len word) states)
    (g : A.TraceRecord p suffix (nth states (len word)) (len suffix) other) :
    ∃ combined : M,
      A.TraceRecord p (Words.append word suffix) initial (len (Words.append word suffix)) combined ∧
      nth combined (len (Words.append word suffix)) = nth other (len suffix) := by
  rcases nil_or_adjoin other with hz | ⟨bridge, tail, ho⟩
  · rw [hz] at g
    have hl := g.1
    simp at hl
  · subst other
    have hbridge : bridge = nth states (len word) := by simpa using g.2.2.1
    have htail : len tail = len suffix := by simpa using g.1
    have hleft : ∀ i ≤ len word,
        nth (Words.append states tail) i = nth states i := by
      intro i hi
      apply Words.nth_append_left
      rw [h.1]
      exact Arithmetic.lt_succ_iff_le.mpr hi
    have hright : ∀ j : M,
        nth (Words.append states tail) (len word + j) = nth (adjoin bridge tail) j := by
      intro j
      rcases zero_or_succ j with rfl | ⟨k, rfl⟩
      · simpa [hbridge] using hleft (len word) (by rfl)
      · have hi : len word + (k + 1) = len states + k := by
          rw [h.1]
          simp [add_assoc, add_comm 1 k]
        rw [hi, Words.nth_append_right]
        simp
    refine ⟨Words.append states tail, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp [Words.len_append, h.1, htail, add_assoc, add_comm 1 (len suffix)]
      · intro i hi
        by_cases hil : i < len states
        · rw [Words.nth_append_left states tail i hil]
          exact h.2.1 i hil
        · have hle : len states ≤ i := le_of_not_gt hil
          obtain ⟨j, rfl⟩ := exists_add_of_le hle
          have hj : j < len tail := by simpa using hi
          rw [Words.nth_append_right]
          have hs := g.2.1 (j + 1) (by simpa using hj)
          simpa using hs
      · rw [hleft 0 (by simp)]
        exact h.2.2.1
      · intro i hi
        by_cases hil : i < len word
        · have hi0 : i ≤ len word := le_of_lt hil
          have hi1 : i + 1 ≤ len word := Arithmetic.succ_le_iff_lt.mpr hil
          rw [Words.nth_append_left word suffix i hil, hleft i hi0, hleft (i + 1) hi1]
          exact h.2.2.2 i hil
        · have hle : len word ≤ i := le_of_not_gt hil
          obtain ⟨j, rfl⟩ := exists_add_of_le hle
          have hj : j < len suffix := by simpa using hi
          have hidx : len word + j + 1 = len word + (j + 1) := by simp [add_assoc]
          rw [Words.nth_append_right, hright j, hidx, hright (j + 1)]
          exact g.2.2.2 j hj
    · rw [Words.len_append, hright]

/-- A final root operation is appended as one actual extra record.
The state vector is extended by arithmetic snoc. -/
theorem traceRecord_snoc {p word initial states record new : M}
    (h : A.TraceRecord p word initial (len word) states)
    (hnew : A.valueStepGraph.val.Evalb ![p, record, nth states (len word), new]) :
    A.TraceRecord p (concat word record) initial (len (concat word record)) (concat states new) ∧
      nth (concat states new) (len (concat word record)) = new := by
  have hn := ((A.valueStepGraph_eval p record (nth states (len word)) new).mp hnew).2.2.1
  constructor
  · refine ⟨by simp [h.1], ?_, ?_, ?_⟩
    · intro i hi
      have hile : i ≤ len states := Arithmetic.lt_succ_iff_le.mp (by simpa using hi)
      rcases lt_or_eq_of_le hile with hil | hieq
      · rw [concat_nth_lt states new hil]
        exact h.2.1 i hil
      · subst i
        simpa using hn
    · rw [concat_nth_lt states new (by rw [h.1]; simp)]
      exact h.2.2.1
    · intro i hi
      have hile : i ≤ len word := Arithmetic.lt_succ_iff_le.mp (by simpa using hi)
      rcases lt_or_eq_of_le hile with hil | hieq
      · have hi0 : i < len states := by rw [h.1]; exact lt_trans hil (by simp)
        have hi1 : i + 1 < len states := by simpa [h.1] using hil
        rw [concat_nth_lt word record hil, concat_nth_lt states new hi0, concat_nth_lt states new hi1]
        exact h.2.2.2 i hil
      · subst i
        rw [concat_nth_len word record, concat_nth_lt states new (by rw [h.1]; simp)]
        rw [← h.1, concat_nth_len]
        exact hnew
  · rw [len_concat, ← h.1, concat_nth_len]

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
