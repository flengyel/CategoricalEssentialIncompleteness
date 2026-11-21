/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceModelLists

/-! # The arithmetic list-snoc code is internal vector concatenation -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.ModelLists
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance modelSnocLocalInstance1 : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance modelSnocLocalInstance2 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance modelSnocLocalInstance3 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance

theorem cons_value {n : ℕ} (A B : Code n) (x l : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (x :> v) (code A))
    (hB : Semiformula.Evalb (l :> v) (code B)) :
    Semiformula.Evalb (adjoin x l :> v) (code (codeListCons A B)) := by
  exact (eval_codeSucc_iff _ _ _).mpr
    ⟨⟪x, l⟫, eval_codePair A B x l v hA hB, rfl⟩

theorem cons_value_iff {n : ℕ} (A B : Code n) (x l o : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (x :> v) (code A))
    (hB : Semiformula.Evalb (l :> v) (code B)) :
    Semiformula.Evalb (o :> v) (code (codeListCons A B)) ↔ o = adjoin x l := by
  constructor
  · exact fun h => eval_unique h (cons_value A B x l v hA hB)
  · rintro rfl
    exact cons_value A B x l v hA hB

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
private theorem code_graph_definable {n : ℕ} (A : Code n) :
    𝚺₁.Definable (fun v : Fin (n + 1) → M => Semiformula.Evalb v (code A)) := by
  let R : 𝚺₁.Semisentence (n + 1) := .mkSigma (code A) (code_sigma_one A)
  exact HierarchySymbol.Defined.to_definable R (.mk (fun _ => Iff.rfl))

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
/-- Only the output and recursion argument vary; the outer input vector
consists of arbitrary model parameters rather than standard numerals. -/
private theorem code_output_index_definable {n : ℕ} (A : Code (n + 1))
    (v : Fin n → M) :
    𝚺₁.Definable (fun w : Fin 2 → M => Semiformula.Evalb (w 0 :> w 1 :> v) (code A)) := by
  let terms : Fin (n + 2) → ArithmeticSemiterm M 2 :=
    Fin.cases #0 (Fin.cases #1 (fun i => &(v i)))
  refine ((code_graph_definable (M := M) A).retractiont (f := terms)).of_iff ?_
  intro w
  have he : (fun i => Semiterm.val w id (terms i)) = w 0 :> w 1 :> v := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [terms]
    · intro j
      refine Fin.cases ?_ ?_ j
      · rfl
      · intro k
        simp [terms]
  rw [he]

/-- Each partial rebuild is the final segment of the original vector,
followed by the new entry. The comparison is internal Pi-one induction. -/
theorem snocCore_value_eq {n : ℕ} (A B : Code n) (l x i o : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (l :> v) (code A))
    (hB : Semiformula.Evalb (x :> v) (code B)) (hi : i ≤ len l)
    (h : Semiformula.Evalb (o :> i :> v) (code (codeListSnocCore A B))) :
    o = concat (takeLast l i) x := by
  have hall : ∀ i : M, i ≤ len l → ∀ o : M,
      Semiformula.Evalb (o :> i :> v) (code (codeListSnocCore A B)) →
        o = concat (takeLast l i) x := by
    intro i
    induction i using ISigma1.pi1_succ_induction
    · apply HierarchySymbol.Definable.imp (by definability)
      apply HierarchySymbol.Definable.all
      exact HierarchySymbol.Definable.imp
        (code_output_index_definable (codeListSnocCore A B) v) (by definability)
    case zero =>
      intro _ o ho
      have hb := eval_codePrec_zero _ _ o v ho
      have hz := (eval_zero_iff (k := n) 0 v).mpr rfl
      simpa using (cons_value_iff B (codeListNil (n := n)) x 0 o v hB hz).mp hb
    case succ i ih =>
      intro hib o ho
      have hil : i < len l := Arithmetic.succ_le_iff_lt.mp hib
      obtain ⟨prev, hp, hs⟩ := eval_codePrec_succ _ _ i o v ho
      have hprev := ih (le_of_lt hil) prev hp
      have hA2 : Semiformula.Evalb (l :> i :> prev :> v)
          (code (codeLift (codeLift A))) :=
        (eval_codeLift_iff _ _ _ _).mpr ((eval_codeLift_iff _ _ _ _).mpr hA)
      have hlen := length_value (codeLift (codeLift A)) l (i :> prev :> v) hA2
      have hsucc : Semiformula.Evalb ((i + 1) :> i :> prev :> v)
          (code (codeSucc (Code.proj (0 : Fin (n + 2))))) :=
        (eval_codeSucc_iff _ _ _).mpr ⟨i, (eval_proj_iff _ _ _).mpr rfl, rfl⟩
      have hindex := eval_codeSub _ _ (len l) (i + 1) (i :> prev :> v) hlen hsucc
      have hj : len l - (i + 1) < len l := (tsub_lt_iff_left hib).mpr (by simp)
      have hget := get_value (codeLift (codeLift A)) _ l (len l - (i + 1))
        (i :> prev :> v) hA2 hindex
      simp only [ite_eq_left hj] at hget
      have hone : Semiformula.Evalb ((1 : M) :> i :> prev :> v)
          (code (codeConst (n := n + 2) 1)) := (eval_codeConst_iff _ _ _).mpr (by simp)
      have hhead := eval_codeSub _ _ (nth l (len l - (i + 1)) + 1) 1
        (i :> prev :> v) hget hone
      rw [add_sub_self] at hhead
      have hrest : Semiformula.Evalb (prev :> i :> prev :> v)
          (code (Code.proj (1 : Fin (n + 2)))) := (eval_proj_iff _ _ _).mpr rfl
      have hcorrect := cons_value _ (Code.proj (1 : Fin (n + 2)))
        (nth l (len l - (i + 1))) prev (i :> prev :> v) hhead hrest
      have hout := eval_unique hs hcorrect
      rw [hout, hprev, takeLast_succ_of_lt hil, concat_adjoin]
  exact hall i hi o h

theorem snoc_value_eq {n : ℕ} (A B : Code n) (l x o : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (l :> v) (code A))
    (hB : Semiformula.Evalb (x :> v) (code B))
    (h : Semiformula.Evalb (o :> v) (code (codeListSnoc A B))) : o = concat l x := by
  rw [codeListSnoc, eval_codeBind_iff] at h
  obtain ⟨i, hi, ho⟩ := h
  have he : i = len l := (length_value_iff A l i v hA).mp hi
  subst i
  simpa only [takeLast_len_self] using snocCore_value_eq A B l x (len l) o v hA hB le_rfl ho

theorem snoc_value {n : ℕ} (A B : Code n) (l x : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (l :> v) (code A))
    (hB : Semiformula.Evalb (x :> v) (code B)) :
    Semiformula.Evalb (concat l x :> v) (code (codeListSnoc A B)) := by
  obtain ⟨o, ho⟩ := eval_codeListSnoc_exists_of_values A B l x v hA hB
  have he := snoc_value_eq A B l x o v hA hB ho
  rwa [he] at ho

theorem snoc_value_iff {n : ℕ} (A B : Code n) (l x o : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (l :> v) (code A))
    (hB : Semiformula.Evalb (x :> v) (code B)) :
    Semiformula.Evalb (o :> v) (code (codeListSnoc A B)) ↔ o = concat l x := by
  constructor
  · exact snoc_value_eq A B l x o v hA hB
  · rintro rfl
    exact snoc_value A B l x v hA hB

end Models
end CategoricalEssentialIncompleteness.V46.UniformTrace.ModelLists
