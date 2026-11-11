/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxEvaluation

/-! # Arithmetic framing of positive finite evaluation records -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

def frameStatusGraph : 𝚺₁.Semisentence 3 :=
  .mkSigma “o status tail. (status = 0 ∧ o = 0) ∨
    (∃ stack out, status = stack + 1 ∧ !Words.appendDef.val out stack tail ∧ o = out + 1)”

def frameVectorBlueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “o tail. o = 0”
  adjoin := .mkSigma “o status states ih tail. ∃ framed,
    !frameStatusGraph.val framed status tail ∧ !adjoinDef.val o framed ih”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance traceDecidableEq : DecidableEq M := Classical.decEq M

noncomputable def frameStatus (status tail : M) : M :=
  if status = 0 then 0 else Words.append (status - 1) tail + 1

@[simp] theorem frameStatus_zero (tail : M) : frameStatus 0 tail = 0 := by simp [frameStatus]
@[simp] theorem frameStatus_succ (stack tail : M) :
    frameStatus (stack + 1) tail = Words.append stack tail + 1 := by simp [frameStatus]

@[simp] theorem frameStatusGraph_eval (o status tail : M) :
    frameStatusGraph.val.Evalb ![o, status, tail] ↔ o = frameStatus status tail := by
  rcases zero_or_succ status with rfl | ⟨stack, rfl⟩ <;> simp [frameStatusGraph]

instance frameStatus_defined :
    𝚺₁-Function₂ (frameStatus : M → M → M) via frameStatusGraph := .mk fun v => by
  have hv : ![v 0, v 1, v 2] = v := (Matrix.fun_eq_vec_three v).symm
  simpa only [hv, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using frameStatusGraph_eval (v 0) (v 1) (v 2)
instance frameStatus_definable : 𝚺₁-Function₂ (frameStatus : M → M → M) :=
  frameStatus_defined.to_definable
instance frameStatus_definable' (Γ m) : Γ-[m + 1]-Function₂ (frameStatus : M → M → M) :=
  frameStatus_definable.of_sigmaOne

def frameVectorConstruction : VecRec.Construction M frameVectorBlueprint where
  nil _ := 0
  adjoin v status _ ih := adjoin (frameStatus status (v 0)) ih
  nil_defined := .mk fun v => by simp [frameVectorBlueprint]
  adjoin_defined := .mk fun v => by simp [frameVectorBlueprint]

/-- This is a numerical vector construction in every PA model. It is
not an external List.map on standard finite records. -/
noncomputable def frameVector (states tail : M) : M := frameVectorConstruction.result ![tail] states

@[simp] theorem frameVector_nil (tail : M) : frameVector 0 tail = 0 := by
  simp [frameVector, frameVectorConstruction]
@[simp] theorem frameVector_adjoin (status states tail : M) :
    frameVector (adjoin status states) tail = adjoin (frameStatus status tail) (frameVector states tail) := by
  simp [frameVector, frameVectorConstruction]
end Models

def frameVectorGraph : 𝚺₁.Semisentence 3 := frameVectorBlueprint.resultDef

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem frameVectorGraph_eval (o states tail : M) :
    frameVectorGraph.val.Evalb ![o, states, tail] ↔ o = frameVector states tail := by
  have hp : (fun i : Fin 1 => (![o, states, tail] : Fin 3 → M) i.succ.succ) = ![tail] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  have he := (frameVectorConstruction (M := M)).eval_resultDef ![o, states, tail]
  rw [hp] at he
  change frameVectorBlueprint.resultDef.val.Evalb ![o, states, tail] ↔
    o = frameVectorConstruction.result ![tail] states
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using he

instance frameVector_defined :
    𝚺₁-Function₂ (frameVector : M → M → M) via frameVectorGraph := .mk fun v => by
  have hv : ![v 0, v 1, v 2] = v := (Matrix.fun_eq_vec_three v).symm
  simpa only [hv, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using frameVectorGraph_eval (v 0) (v 1) (v 2)

instance frameVector_definable : 𝚺₁-Function₂ (frameVector : M → M → M) := frameVector_defined.to_definable
instance frameVector_definable' (Γ m) : Γ-[m + 1]-Function₂ (frameVector : M → M → M) :=
  frameVector_definable.of_sigmaOne

@[simp] theorem len_frameVector (states tail : M) : len (frameVector states tail) = len states := by
  induction states using adjoin_ISigma1.pi1_succ_induction
  · definability
  case nil => simp
  case adjoin x states ih => simp [ih]

theorem nth_frameVector (states tail i : M) (hi : i < len states) :
    nth (frameVector states tail) i = frameStatus (nth states i) tail := by
  induction states using adjoin_ISigma1.pi1_succ_induction generalizing i
  · definability
  case nil => simp at hi
  case adjoin x states ih =>
    rcases zero_or_succ i with rfl | ⟨j, rfl⟩
    · simp
    · have hj : j < len states := by simpa using hi
      simpa using ih j hj

/-- Positive common-fiber membership is stable under appending an
already supplied ambient tail in that same parameter fiber. -/
theorem fiberStack_append (P X Y : Carrier) (ξ υ : FailureOfComposition.ProofSearch.Graph)
    (p stack tail : M)
    (hs : (fiberStackGraph P X Y ξ υ).val.Evalb ![p, stack])
    (ht : (fiberStackGraph P X Y ξ υ).val.Evalb ![p, tail]) :
    (fiberStackGraph P X Y ξ υ).val.Evalb ![p, Words.append stack tail] := by
  rw [fiberStackGraph_eval] at hs ht ⊢
  intro i hi
  by_cases hil : i < len stack
  · simpa only [Words.nth_append_left stack tail i hil] using hs i hil
  · have hle : len stack ≤ i := le_of_not_gt hil
    obtain ⟨j, rfl⟩ := exists_add_of_le hle
    have hj : j < len tail := by simpa using hi
    simpa only [Words.nth_append_right] using ht j hj

theorem frameStatus_fiber (P X Y : Carrier) (ξ υ : FailureOfComposition.ProofSearch.Graph)
    (p status tail : M)
    (hs : (statusGraph P X Y ξ υ).val.Evalb ![p, status])
    (ht : (fiberStackGraph P X Y ξ υ).val.Evalb ![p, tail]) :
    (statusGraph P X Y ξ υ).val.Evalb ![p, frameStatus status tail] := by
  obtain ⟨hp, hst⟩ := (statusGraph_eval P X Y ξ υ p status).mp hs
  rcases zero_or_succ status with rfl | ⟨stack, rfl⟩
  · simp [hp]
  · have hsf : (fiberStackGraph P X Y ξ υ).val.Evalb ![p, stack] := by simpa using hst
    simpa [hp] using fiberStack_append P X Y ξ υ p stack tail hsf ht

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
open Coding
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Error is absorbing throughout an actual finite record. The proof
uses internal Pi-one induction, with arbitrary model index i. -/
theorem ValueRecord.error_suffix {p word n states i : M}
    (h : A.ValueRecord p word n states) (hi : i ≤ n) (hz : nth states i = 0) :
    nth states n = 0 := by
  have hh : ∀ j ≤ n, i ≤ j → nth states j = 0 := by
    intro j hj hij
    induction j using ISigma1.pi1_succ_induction
    · definability
    case zero =>
      have hi0 : i = 0 := by simpa using hij
      simpa [hi0] using hz
    case succ j ih =>
      by_cases he : i = j + 1
      · simpa [he] using hz
      · have hij' : i ≤ j := Arithmetic.lt_succ_iff_le.mp (lt_of_le_of_ne hij he)
        have hprev := ih (le_trans (by simp) hj) hij'
        have hstep := h.2.2.2 j (Arithmetic.succ_le_iff_lt.mp hj)
        rw [hprev] at hstep
        exact ((A.valueStepGraph_zero p (nth word j) (nth states (j + 1))).mp hstep).2.2
  exact hh n (by rfl) hi

theorem ValueRecord.prefix_ne_zero {p word n states : M}
    (h : A.ValueRecord p word n states) (hend : nth states n ≠ 0)
    (i : M) (hi : i ≤ n) : nth states i ≠ 0 := by
  intro hz
  exact hend (ValueRecord.error_suffix A h hi hz)

/-- Every framed step has an original successful refill, so the
pre-existing ambient tail cannot supply a missing child. The supplied
operation trace and reconstructed raw input are retained unchanged. -/
theorem valueStep_frame (p record old new tail : M)
    (h : A.valueStepGraph.val.Evalb ![p, record, old, new])
    (hnew : new ≠ 0)
    (ht : (fiberStackGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, tail]) :
    A.valueStepGraph.val.Evalb ![p, record, frameStatus old tail, frameStatus new tail] := by
  obtain ⟨hr, hold, hn, hc⟩ := (A.valueStepGraph_eval p record old new).mp h
  have hsf := frameStatus_fiber P X Y A.termProjection.graph A.formulaProjection.graph p old tail hold ht
  have hnf := frameStatus_fiber P X Y A.termProjection.graph A.formulaProjection.graph p new tail hn ht
  rcases hc with ⟨_, hz⟩ | ⟨s, stack, rfl, rfl, ho⟩ | ⟨s, stack, rfl, rfl, ho⟩
  · exact False.elim (hnew hz)
  · rcases ho with ⟨_, hz⟩ | ⟨u, rest, value, hu, hv, rfl⟩
    · exact False.elim (hnew hz)
    · simp only [frameStatus_succ] at hsf hnf ⊢
      apply (A.valueStepGraph_term p s (Words.append stack tail) _).mpr
      refine ⟨by simpa using hr, by simpa using hsf, by simpa using hnf, ?_⟩
      exact Or.inr ⟨u, Words.append rest tail, value,
        refill_frame a s stack u rest tail hu, hv, by simp⟩
  · rcases ho with ⟨_, hz⟩ | ⟨u, rest, value, hu, hv, rfl⟩
    · exact False.elim (hnew hz)
    · simp only [frameStatus_succ] at hsf hnf ⊢
      apply (A.valueStepGraph_formula p s (Words.append stack tail) _).mpr
      refine ⟨by simpa using hr, by simpa using hsf, by simpa using hnf, ?_⟩
      exact Or.inr ⟨u, Words.append rest tail, value,
        refill_frame b s stack u rest tail hu, hv, by simp⟩

/-- A trace starts at a displayed numerical status, so actual child
computations can be framed and concatenated in printed word order. -/
def traceRecordGraph : 𝚺₁.Semisentence 5 :=
  let S := statusGraph P X Y A.termProjection.graph A.formulaProjection.graph
  let R := A.valueStepGraph
  .mkSigma “p word initial n states. ∃ l, !lenDef.val l states ∧ l = n + 1 ∧
    (∀ i < l, ∃ z, !nthDef.val z states i ∧ !S.val p z) ∧
    !nthDef.val initial states 0 ∧
    ∀ i < n, ∃ v x y, !nthDef.val v word i ∧
      !nthDef.val x states i ∧ !nthDef.val y states (i + 1) ∧ !R.val p v x y”

def TraceRecord (p word initial n states : M) : Prop :=
  len states = n + 1 ∧
    (∀ i < len states,
      (statusGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, nth states i]) ∧
    nth states 0 = initial ∧ ∀ i < n,
      A.valueStepGraph.val.Evalb ![p, nth word i, nth states i, nth states (i + 1)]

@[simp] theorem traceRecordGraph_eval (p word initial n states : M) :
    A.traceRecordGraph.val.Evalb ![p, word, initial, n, states] ↔
      A.TraceRecord p word initial n states := by
  simp [traceRecordGraph, TraceRecord, eq_comm]

@[simp] theorem traceRecord_one (p word n states : M) :
    A.TraceRecord p word 1 n states ↔ A.ValueRecord p word n states := Iff.rfl

/-- Numerical vector framing transforms every state of a successful
child record and preserves every positive operation witness. -/
theorem valueRecord_frame {p word n states tail : M}
    (h : A.ValueRecord p word n states) (hend : nth states n ≠ 0)
    (ht : (fiberStackGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, tail]) :
    A.TraceRecord p word (tail + 1) n (frameVector states tail) := by
  refine ⟨by simp [h.1], ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i < len states := by simpa using hi
    rw [nth_frameVector states tail i hi']
    exact frameStatus_fiber P X Y A.termProjection.graph A.formulaProjection.graph
      p (nth states i) tail (h.2.1 i hi') ht
  · rw [nth_frameVector states tail 0 (by rw [h.1]; simp), h.2.2.1]
    simp [frameStatus]
  · intro i hi
    have hi0 : i < len states := by rw [h.1]; exact lt_trans hi (by simp)
    have hi1 : i + 1 < len states := by simpa [h.1] using hi
    rw [nth_frameVector states tail i hi0, nth_frameVector states tail (i + 1) hi1]
    exact A.valueStep_frame p (nth word i) (nth states i) (nth states (i + 1)) tail
      (h.2.2.2 i hi) (ValueRecord.prefix_ne_zero A h hend (i + 1) (Arithmetic.succ_le_iff_lt.mpr hi)) ht

theorem TraceRecord.zero (p word initial : M)
    (hi : (statusGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, initial]) :
    A.TraceRecord p word initial 0 (adjoin initial 0) := by
  refine ⟨by simp, ?_, by simp, ?_⟩
  · intro i hi'
    have hi0 : i = 0 := by simpa using hi'
    simpa [hi0] using hi
  · intro i hi'
    simp at hi'


end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
