/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxState

/-! # Actual finite state-and-operation records for postfix evaluation -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
open Coding
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)

/-- Index zero is the empty value stack. At index i+1 the record stores
the result after reading input position i. All actual root-operation
traces occur positively inside valueStepGraph. -/
def valueRecordGraph : 𝚺₁.Semisentence 4 :=
  let S := statusGraph P X Y A.termProjection.graph A.formulaProjection.graph
  let R := A.valueStepGraph
  .mkSigma “p word n states. ∃ l, !lenDef.val l states ∧ l = n + 1 ∧
    (∀ i < l, ∃ z, !nthDef.val z states i ∧ !S.val p z) ∧
    !nthDef.val 1 states 0 ∧
    ∀ i < n, ∃ v x y, !nthDef.val v word i ∧
      !nthDef.val x states i ∧ !nthDef.val y states (i + 1) ∧ !R.val p v x y”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* T]

/-- This is the numerical finite record itself, not an assumed fold. -/
def ValueRecord (p word n states : M) : Prop :=
  len states = n + 1 ∧
    (∀ i < len states,
      (statusGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, nth states i]) ∧
    nth states 0 = 1 ∧ ∀ i < n,
      A.valueStepGraph.val.Evalb ![p, nth word i, nth states i, nth states (i + 1)]

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem valueRecordGraph_eval (p word n states : M) :
    A.valueRecordGraph.val.Evalb ![p, word, n, states] ↔ A.ValueRecord p word n states := by
  simp [valueRecordGraph, ValueRecord, eq_comm]

omit [M↓[ℒₒᵣ] ⊧* T] in
instance valueRecord_definable :
    𝚺₁.Definable (fun v : Fin 4 → M => A.ValueRecord (v 0) (v 1) (v 2) (v 3)) := by
  refine ⟨A.valueRecordGraph.rew Rew.emb, ?_⟩
  intro v
  have hv : ![v 0, v 1, v 2, v 3] = v := (Matrix.fun_eq_vec_four v).symm
  simpa [hv] using A.valueRecordGraph_eval (v 0) (v 1) (v 2) (v 3)

omit [M↓[ℒₒᵣ] ⊧* T] in
theorem valueRecord_zero (p word : M) (hp : P.val.Evalb ![p]) :
    A.ValueRecord p word 0 (adjoin 1 0) := by
  refine ⟨by simp, ?_, by simp, ?_⟩
  · intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst i
    simp [hp]
  · intro i hi
    simp at hi

omit [M↓[ℒₒᵣ] ⊧* T] in
/-- Extending the state vector appends one computed value. Reads before
its final index retain exactly the previous finite record. -/
theorem valueRecord_append {p word n states new : M}
    (h : A.ValueRecord p word n states)
    (hnew : A.valueStepGraph.val.Evalb ![p, nth word n, nth states n, new]) :
    A.ValueRecord p word (n + 1) (concat states new) := by
  have hnewf := ((A.valueStepGraph_eval p (nth word n) (nth states n) new).mp hnew).2.2.1
  refine ⟨by simp [h.1], ?_, ?_, ?_⟩
  · intro i hi
    have hile : i ≤ len states := Arithmetic.lt_succ_iff_le.mp (by simpa using hi)
    rcases lt_or_eq_of_le hile with hil | rfl
    · simpa only [concat_nth_lt states new hil] using h.2.1 i hil
    · simpa using hnewf
  · rw [concat_nth_lt states new (by rw [h.1]; simp)]
    exact h.2.2.1
  · intro i hi
    have hile : i ≤ n := Arithmetic.lt_succ_iff_le.mp hi
    rcases lt_or_eq_of_le hile with hil | hieq
    · have hi0 : i < len states := by rw [h.1]; exact lt_trans hil (by simp)
      have hi1 : i + 1 < len states := by simpa [h.1] using hil
      simpa only [concat_nth_lt states new hi0, concat_nth_lt states new hi1] using h.2.2.2 i hil
    · subst i
      have hn : n < len states := by rw [h.1]; simp
      simpa only [concat_nth_lt states new hn, ← h.1, concat_nth_len] using hnew

/-- Internal Sigma-one induction on the actual number of input records
constructs all operation witnesses and states, including at nonstandard
lengths. No total evaluator is supplied as an assumption. -/
theorem valueRecord_exists (p word : M) (hp : P.val.Evalb ![p])
    (hword : (coefficients a b).val.Evalb ![word]) :
    ∃ states : M, A.ValueRecord p word (len word) states := by
  have hc : ∀ i < len word, (recordCarrier a b).val.Evalb ![nth word i] := by
    exact (FiniteSigmaOne.allEntriesCondition_eval (recordCarrier a b) word).mp
      ((FiniteSigmaOne.finite_membership_model (recordCarrier a b) word).mpr hword)
  have hh : ∀ n ≤ len word, ∃ states : M, A.ValueRecord p word n states := by
    intro n hn
    induction n using ISigma1.sigma1_succ_induction
    · definability
    case zero => exact ⟨adjoin 1 0, A.valueRecord_zero p word hp⟩
    case succ n ih =>
      have hnlt : n < len word := Arithmetic.succ_le_iff_lt.mp hn
      obtain ⟨states, hs⟩ := ih (le_trans (by simp) hn)
      have hnf := hs.2.1 n (by rw [hs.1]; simp)
      obtain ⟨new, hnew, _⟩ := A.valueStep_existsUnique p (nth word n) (nth states n) (hc n hnlt) hnf
      exact ⟨concat states new, A.valueRecord_append hs hnew⟩
  exact hh (len word) (by rfl)

/-- Pi-one induction compares every pair of displayed states, using the
actual graph-operation functionality at each successor position. -/
theorem valueRecord_unique {p word n states other : M}
    (h : A.ValueRecord p word n states) (g : A.ValueRecord p word n other) :
    nth states n = nth other n := by
  have he : ∀ i ≤ n, nth states i = nth other i := by
    intro i hi
    induction i using ISigma1.pi1_succ_induction
    · definability
    case zero => exact h.2.2.1.trans g.2.2.1.symm
    case succ i ih =>
      have hil : i < n := Arithmetic.succ_le_iff_lt.mp hi
      have hprev := ih (le_trans (by simp) hi)
      have hs := h.2.2.2 i hil
      have gs := g.2.2.2 i hil
      rw [← hprev] at gs
      have hx := ((A.valueStepGraph_eval p (nth word i) (nth states i) (nth states (i + 1))).mp hs)
      exact (A.valueStep_existsUnique p (nth word i) (nth states i) hx.1 hx.2.1).unique hs gs
  exact he n (by rfl)

end Models

/-- The output is selected from an explicit finite vector of states.
Error is retained at this general loop stage; acceptance later excludes
it and identifies the unique value of the requested syntax sort. -/
def loopEvaluationGraph : 𝚺₁.Semisentence 3 :=
  let C := coefficients a b
  let R := A.valueRecordGraph
  .mkSigma “p word status. !P.val p ∧ !C.val word ∧
    ∃ n states, !lenDef.val n word ∧ !R.val p word n states ∧ !nthDef.val status states n”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* T]

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem loopEvaluationGraph_eval (p word status : M) :
    A.loopEvaluationGraph.val.Evalb ![p, word, status] ↔
      P.val.Evalb ![p] ∧ (coefficients a b).val.Evalb ![word] ∧
        ∃ states : M, A.ValueRecord p word (len word) states ∧ status = nth states (len word) := by
  simp [loopEvaluationGraph]

/-- Arbitrary graph-defined slice operations have a unique
finite computation on every coefficient-valid literal input word. -/
theorem loopEvaluation_existsUnique (p word : M) (hp : P.val.Evalb ![p])
    (hw : (coefficients a b).val.Evalb ![word]) :
    ∃! status : M, A.loopEvaluationGraph.val.Evalb ![p, word, status] := by
  obtain ⟨states, hs⟩ := A.valueRecord_exists p word hp hw
  refine ⟨nth states (len word), (A.loopEvaluationGraph_eval p word _).mpr
    ⟨hp, hw, states, hs, rfl⟩, ?_⟩
  intro z hz
  obtain ⟨_, _, other, ho, rfl⟩ := (A.loopEvaluationGraph_eval p word z).mp hz
  exact A.valueRecord_unique ho hs

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
