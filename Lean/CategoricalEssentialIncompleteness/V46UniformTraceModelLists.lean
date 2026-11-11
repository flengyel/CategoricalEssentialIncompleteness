/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceCoding

/-! # Reading the actual list codes in arbitrary PA models

The numeric list carrier is the whole model, with its canonical zero/adjoin
decomposition. All inductions here are internal arithmetic inductions; no
standard finite-list decoder or external natural-number bound is used.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.ModelLists

def dropCoreGraph : 𝚺₁.Semisentence 3 :=
  .mkSigma (code codeListDropCore) (code_sigma_one codeListDropCore)

/-- Output, list, and index, in this order. -/
def dropGraph : 𝚺₁.Semisentence 3 :=
  .mkSigma “o l i. !dropCoreGraph.val o i l”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance modelListsLocalInstance1 : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance modelListsLocalInstance2 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance modelListsLocalInstance3 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance
local instance modelListsLocalInstance4 : DecidableEq M := Classical.decEq M
local instance modelListsLocalInstance5 : DecidableLT M := Classical.decRel _

theorem tail_value {n : ℕ} (d : Code n) (l : M) (v : Fin n → M)
    (h : Semiformula.Evalb (l :> v) (code d)) :
    Semiformula.Evalb (sndIdx l :> v) (code (codeListTail d)) := by
  have hsub := eval_codeSub d (codeConst 1) l 1 v h
    ((eval_codeConst_iff _ _ _).mpr (by simp))
  exact eval_codeUnpair₂ _ (l - 1) v hsub

theorem drop_exists (l i : M) :
    ∃ z : M, Semiformula.Evalb ![z, i, l] (code codeListDropCore) := by
  exact eval_codePrec_exists_of_total (Code.proj (0 : Fin 1))
    (codeListTail (Code.proj (1 : Fin 3))) i ![l]
    ⟨l, (eval_proj_iff _ _ _).mpr rfl⟩
    (fun j _ z => ⟨sndIdx z,
      tail_value _ z ![j, z, l] ((eval_proj_iff _ _ _).mpr rfl)⟩)

/-- This chosen function is backed by the actual total list-drop code.
Its graph and its arithmetic recursion equations are proved below. -/
noncomputable def drop (l i : M) : M := Classical.choose (drop_exists l i)

theorem drop_spec (l i : M) :
    Semiformula.Evalb ![drop l i, i, l] (code codeListDropCore) :=
  Classical.choose_spec (drop_exists l i)

@[simp] theorem dropCore_eval (o i l : M) :
    Semiformula.Evalb ![o, i, l] (code codeListDropCore) ↔ o = drop l i := by
  constructor
  · intro h
    exact eval_unique h (drop_spec l i)
  · rintro rfl
    exact drop_spec l i

@[simp] theorem dropGraph_eval (o l i : M) :
    dropGraph.val.Evalb ![o, l, i] ↔ o = drop l i := by
  simp [dropGraph, dropCoreGraph, dropCore_eval]

instance drop_defined : 𝚺₁-Function₂ (drop : M → M → M) via dropGraph := .mk fun v => by
  have hv : ![v 0, v 1, v 2] = v := (Matrix.fun_eq_vec_three v).symm
  simpa only [hv, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using
    dropGraph_eval (v 0) (v 1) (v 2)
instance drop_definable : 𝚺₁-Function₂ (drop : M → M → M) := drop_defined.to_definable
instance drop_definable' (Γ m) : Γ-[m + 1]-Function₂ (drop : M → M → M) :=
  drop_definable.of_sigmaOne

@[simp] theorem drop_zero (l : M) : drop l 0 = l := by
  have h := eval_codePrec_zero (Code.proj (0 : Fin 1))
    (codeListTail (Code.proj (1 : Fin 3))) (drop l 0) ![l] (drop_spec l 0)
  exact (eval_proj_iff _ _ _).mp h

@[simp] theorem drop_succ (l i : M) : drop l (i + 1) = sndIdx (drop l i) := by
  obtain ⟨z, hz, hs⟩ := eval_codePrec_succ (Code.proj (0 : Fin 1))
    (codeListTail (Code.proj (1 : Fin 3))) i (drop l (i + 1)) ![l] (drop_spec l (i + 1))
  have he : z = drop l i := (dropCore_eval z i l).mp hz
  subst z
  exact eval_unique hs
    (tail_value _ (drop l i) ![i, drop l i, l] ((eval_proj_iff _ _ _).mpr rfl))

@[simp] theorem drop_nil (i : M) : drop 0 i = 0 := by
  induction i using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ i ih => simp [ih, sndIdx, pi₂_zero]

@[simp] theorem drop_adjoin_succ (x l i : M) :
    drop (adjoin x l) (i + 1) = drop l i := by
  induction i using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    simpa only [drop_zero, sndIdx_adjoin] using drop_succ (adjoin x l) (0 : M)
  case succ i ih => rw [drop_succ (adjoin x l) (i + 1), ih, drop_succ l i]

theorem drop_eq_zero_iff (l i : M) : drop l i = 0 ↔ len l ≤ i := by
  induction l using adjoin_ISigma1.pi1_succ_induction generalizing i
  · definability
  case nil => simp
  case adjoin x l ih =>
    rcases zero_or_succ i with rfl | ⟨i, rfl⟩
    · simp
    · simp only [drop_adjoin_succ, len_adjoin, add_le_add_iff_right]
      exact ih i

theorem drop_ne_zero_iff (l i : M) : drop l i ≠ 0 ↔ i < len l := by
  constructor
  · intro hn
    by_contra hi
    exact hn ((drop_eq_zero_iff l i).mpr (le_of_not_gt hi))
  · intro hi hz
    exact (not_le.mpr hi) ((drop_eq_zero_iff l i).mp hz)

theorem head_drop (l i : M) : fstIdx (drop l i) = nth l i := by
  induction l using adjoin_ISigma1.pi1_succ_induction generalizing i
  · definability
  case nil => simp [fstIdx, pi₁_zero]
  case adjoin x l ih =>
    rcases zero_or_succ i with rfl | ⟨i, rfl⟩
    · simp
    · simpa only [drop_adjoin_succ, nth_adjoin_succ] using ih i

theorem drop_value {n : ℕ} (A B : Code n) (l i : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (l :> v) (code A))
    (hB : Semiformula.Evalb (i :> v) (code B)) :
    Semiformula.Evalb (drop l i :> v) (code (codeListDrop A B)) := by
  rw [codeListDrop_eq_comp, eval_comp_iff]
  refine ⟨![i, l], drop_spec l i, ?_⟩
  intro j
  fin_cases j
  · exact hB
  · exact hA

theorem drop_value_iff {n : ℕ} (A B : Code n) (l i o : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (l :> v) (code A))
    (hB : Semiformula.Evalb (i :> v) (code B)) :
    Semiformula.Evalb (o :> v) (code (codeListDrop A B)) ↔ o = drop l i := by
  constructor
  · exact fun h => eval_unique h (drop_value A B l i v hA hB)
  · rintro rfl
    exact drop_value A B l i v hA hB

/-- The literal minimization code returns Foundation's internal length
on every model element. Earlier failures come from the proved zero-tail law. -/
theorem length_value {n : ℕ} (A : Code n) (l : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (l :> v) (code A)) :
    Semiformula.Evalb (len l :> v) (code (codeListLength A)) := by
  have hd (i : M) : Semiformula.Evalb (drop l i :> i :> v)
      (code (codeListDrop (codeLift A) (codeHead (n := n)))) :=
    drop_value _ _ l i (i :> v) ((eval_codeLift_iff _ _ _ _).mpr hA)
      ((eval_codeHead_iff _ _).mpr rfl)
  rw [codeListLength, eval_codeRfindPos_iff]
  constructor
  · refine ⟨1, by simp, (eval_codeInv_iff _ _ _).mpr ⟨drop l (len l), hd (len l), ?_⟩⟩
    exact Or.inl ⟨(drop_eq_zero_iff l (len l)).mpr le_rfl, rfl⟩
  · intro i hi
    apply (eval_codeInv_iff _ _ _).mpr
    exact ⟨drop l i, hd i, Or.inr ⟨(drop_ne_zero_iff l i).mpr hi, rfl⟩⟩

theorem length_value_iff {n : ℕ} (A : Code n) (l o : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (l :> v) (code A)) :
    Semiformula.Evalb (o :> v) (code (codeListLength A)) ↔ o = len l := by
  constructor
  · exact fun h => eval_unique h (length_value A l v hA)
  · rintro rfl
    exact length_value A l v hA

theorem head_value {n : ℕ} (A : Code n) (l : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (l :> v) (code A)) :
    Semiformula.Evalb ((if l = 0 then 0 else fstIdx l + 1) :> v)
      (code (codeListHead? A)) := by
  have hsub := eval_codeSub A (codeConst 1) l 1 v hA
    ((eval_codeConst_iff _ _ _).mpr (by simp))
  have hh := eval_codeUnpair₁ _ (l - 1) v hsub
  have hsucc := (eval_codeSucc_iff _ _ _).mpr ⟨fstIdx l, hh, rfl⟩
  have hz := (eval_zero_iff (k := n) 0 v).mpr rfl
  rw [codeListHead?]
  by_cases hl : l = 0
  · simp only [hl, ite_eq_left]
    exact eval_codeIfPos_of _ _ _ l (fstIdx l + 1) 0 0 v hA hsucc hz
      (Or.inr ⟨hl, rfl⟩)
  · simp only [ite_eq_right hl]
    exact eval_codeIfPos_of _ _ _ l (fstIdx l + 1) 0 (fstIdx l + 1) v hA hsucc hz
      (Or.inl ⟨lt_of_le_of_ne (FFL.FirstOrder.Arithmetic.zero_le l) (Ne.symm hl), rfl⟩)

theorem get_value {n : ℕ} (A B : Code n) (l i : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (l :> v) (code A))
    (hB : Semiformula.Evalb (i :> v) (code B)) :
    Semiformula.Evalb ((if i < len l then nth l i + 1 else 0) :> v)
      (code (codeListGet? A B)) := by
  have hh := head_value (codeListDrop A B) (drop l i) v (drop_value A B l i v hA hB)
  by_cases hi : i < len l
  · have hn := (drop_ne_zero_iff l i).mpr hi
    simpa only [codeListGet?, ite_eq_left hi, ite_eq_right hn, head_drop] using hh
  · have hz := (drop_eq_zero_iff l i).mpr (le_of_not_gt hi)
    simpa only [codeListGet?, ite_eq_right hi, hz, ite_eq_left rfl, ite_true] using hh

theorem get_value_iff {n : ℕ} (A B : Code n) (l i o : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (l :> v) (code A))
    (hB : Semiformula.Evalb (i :> v) (code B)) :
    Semiformula.Evalb (o :> v) (code (codeListGet? A B)) ↔
      o = if i < len l then nth l i + 1 else 0 := by
  constructor
  · exact fun h => eval_unique h (get_value A B l i v hA hB)
  · rintro rfl
    exact get_value A B l i v hA hB

end Models
end CategoricalEssentialIncompleteness.V46.UniformTrace.ModelLists
