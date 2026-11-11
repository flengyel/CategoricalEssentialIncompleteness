/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceDecoder
public import CategoricalEssentialIncompleteness.V46UniformTraceModelHistory
public import CategoricalEssentialIncompleteness.V46UniformTraceProgram
public import CategoricalRiceShapiro.Evaluator.CompositionDispatch

/-! # Composition-stage certificates for arbitrary internal component indices

This is the raw same-stage constructor equation. The later fixed-template
compiler uses this equation together with fixed-standard-index persistence.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator

namespace CategoricalEssentialIncompleteness.V46.UniformTrace
open ProgramIndices ModelHistory
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance compositionLocalInstance1 : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance compositionLocalInstance2 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance compositionLocalInstance3 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance

theorem select_if_positive {n : ℕ} (C A B : Code n) (c o : M) (v : Fin n → M)
    (hC : Semiformula.Evalb (c :> v) (code C)) (hc : 0 < c)
    (h : Semiformula.Evalb (o :> v) (code (codeIfPos C A B))) :
    Semiformula.Evalb (o :> v) (code A) := by
  obtain ⟨c', hc', hcase⟩ := eval_codeIfPos_cases C A B o v h
  have he : c' = c := eval_unique hc' hC
  rw [he] at hcase
  exact (hcase.resolve_right (fun hz => (ne_of_gt hc) hz.1)).2

theorem select_if_zero {n : ℕ} (C A B : Code n) (o : M) (v : Fin n → M)
    (hC : Semiformula.Evalb ((0 : M) :> v) (code C))
    (h : Semiformula.Evalb (o :> v) (code (codeIfPos C A B))) :
    Semiformula.Evalb (o :> v) (code B) := by
  obtain ⟨c, hc, hcase⟩ := eval_codeIfPos_cases C A B o v h
  have he : c = 0 := eval_unique hc hC
  rw [he] at hcase
  exact (hcase.resolve_left (fun hp => (Arithmetic.lt_irrefl (0 : M)) hp.1)).2

/-- Positive fuel and the actual tag graph force the composition branch,
including when the whole cell's supplied output is zero. -/
theorem select_comp_branch {n : ℕ} (A X : Code n) (fuel o : M) (v : Fin n → M)
    (hFuel : Semiformula.Evalb (fuel :> v) (code (codeUnpair₁ (codeListLength A))))
    (hf : 0 < fuel)
    (hTag : Semiformula.Evalb ((5 : M) :> v)
      (code (codePartrecTag (codeUnpair₂ (codeListLength A)))))
    (h : Semiformula.Evalb (o :> v) (code (codeEvaluatorCell A X))) :
    Semiformula.Evalb (o :> v) (code (codeCompEvaluatorCell A
      (codeUnpair₁ (codeListLength A))
      (codePartrecPayload₁ (codeUnpair₂ (codeListLength A)))
      (codePartrecPayload₂ (codeUnpair₂ (codeListLength A))) X)) := by
  have h4 : Semiformula.Evalb ((4 : M) :> v) (code (codeConst (n := n) 4)) :=
    (eval_codeConst_iff _ _ _).mpr (by simp)
  have h5 : Semiformula.Evalb ((5 : M) :> v) (code (codeConst (n := n) 5)) :=
    (eval_codeConst_iff _ _ _).mpr (by simp)
  let K := codeUnpair₁ (codeListLength A)
  let Q := codeUnpair₂ (codeListLength A)
  let Tag := codePartrecTag Q
  let Left := codePartrecPayload₁ Q
  let Right := codePartrecPayload₂ Q
  let PairBranch := codePairEvaluatorCell A K Left Right X
  let CompBranch := codeCompEvaluatorCell A K Left Right X
  let Later := codeIfPos (codeEq Tag (codeConst 6))
    (codePrecEvaluatorCell A (codeSub K (codeConst 1)) Q Left Right X)
    (codeIfPos (codeEq Tag (codeConst 7))
      (codeRfindEvaluatorCell A (codeSub K (codeConst 1)) Q (codePartrecPayload Q) X)
      (codeBaseEvaluatorCell A X))
  have htest4 := eq_value Tag (codeConst 4) (5 : M) 4 v hTag h4
  have htest5 := eq_value Tag (codeConst 5) (5 : M) 5 v hTag h5
  simp only [show ¬(5 : M) = 4 by norm_num, ite_false] at htest4
  simp only at htest5
  have hbig := select_if_positive K
    (codeIfPos (codeEq Tag (codeConst 4)) PairBranch
      (codeIfPos (codeEq Tag (codeConst 5)) CompBranch Later))
    (codeConst 0) fuel o v hFuel hf h
  have hrest := select_if_zero (codeEq Tag (codeConst 4)) PairBranch
    (codeIfPos (codeEq Tag (codeConst 5)) CompBranch Later) o v htest4 hbig
  exact select_if_positive (codeEq Tag (codeConst 5)) CompBranch Later
    1 o v htest5 (by simp) hrest

theorem build_comp_cell {n : ℕ} (A X : Code n) (table input fuel o : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (table :> v) (code A))
    (hX : Semiformula.Evalb (input :> v) (code X))
    (hFuel : Semiformula.Evalb (fuel :> v) (code (codeUnpair₁ (codeListLength A))))
    (hf : 0 < fuel)
    (hTag : Semiformula.Evalb ((5 : M) :> v)
      (code (codePartrecTag (codeUnpair₂ (codeListLength A)))))
    (hBranch : Semiformula.Evalb (o :> v) (code (codeCompEvaluatorCell A
      (codeUnpair₁ (codeListLength A))
      (codePartrecPayload₁ (codeUnpair₂ (codeListLength A)))
      (codePartrecPayload₂ (codeUnpair₂ (codeListLength A))) X))) :
    Semiformula.Evalb (o :> v) (code (codeEvaluatorCell A X)) := by
  obtain ⟨z, hz⟩ := eval_codeEvaluatorCell_exists_of_values A X table input v hA hX
  have hb := select_comp_branch A X fuel z v hFuel hf hTag hz
  have he : z = o := eval_unique hb hBranch
  rwa [he] at hz

theorem compIndex_left_lt (f g : M) : f < compIndex f g := by
  have hp : ⟪f, g⟫ ≤ 4 * ⟪f, g⟫ := by
    calc
      ⟪f, g⟫ = 1 * ⟪f, g⟫ := by simp
      _ ≤ 4 * ⟪f, g⟫ := mul_le_mul_right (by norm_num : (1 : M) ≤ 4)
  calc
    f ≤ ⟪f, g⟫ := le_pair_left _ _
    _ < ⟪f, g⟫ + 1 := by simp
    _ ≤ 4 * ⟪f, g⟫ + 1 := by
      simpa only [add_comm] using add_le_add_right hp 1
    _ ≤ 4 * ⟪f, g⟫ + 6 := by
      simpa only [add_comm] using
        add_le_add_left (by norm_num : (1 : M) ≤ 6) (4 * ⟪f, g⟫)
    _ = compIndex f g := by
      change 4 * ⟪f, g⟫ + 6 = (4 + 4 * ⟪f, g⟫) + 2
      rw [add_comm (4 : M) (4 * ⟪f, g⟫), add_assoc]
      norm_num

theorem compIndex_right_lt (f g : M) : g < compIndex f g := by
  have hp : ⟪f, g⟫ ≤ 4 * ⟪f, g⟫ := by
    calc
      ⟪f, g⟫ = 1 * ⟪f, g⟫ := by simp
      _ ≤ 4 * ⟪f, g⟫ := mul_le_mul_right (by norm_num : (1 : M) ≤ 4)
  calc
    g ≤ ⟪f, g⟫ := le_pair_right _ _
    _ < ⟪f, g⟫ + 1 := by simp
    _ ≤ 4 * ⟪f, g⟫ + 1 := by
      simpa only [add_comm] using add_le_add_right hp 1
    _ ≤ 4 * ⟪f, g⟫ + 6 := by
      simpa only [add_comm] using
        add_le_add_left (by norm_num : (1 : M) ≤ 6) (4 * ⟪f, g⟫)
    _ = compIndex f g := by
      change 4 * ⟪f, g⟫ + 6 = (4 + 4 * ⟪f, g⟫) + 2
      rw [add_comm (4 : M) (4 * ⟪f, g⟫), add_assoc]
      norm_num

/-- Both components of a literal composition certificate are read at
the same stage, with no external natural-number index parameters. -/
theorem composition_stage_iff (s f g input output : M) :
    evalnGraphFormula.val.Evalb ![output + 1, s, compIndex f g, input] ↔
      ∃ middle : M, evalnGraphFormula.val.Evalb ![middle + 1, s, g, input] ∧
        evalnGraphFormula.val.Evalb ![output + 1, s, f, middle] := by
  let q := compIndex f g
  let v : Fin 3 → M := ![s, q, input]
  obtain ⟨H, hBefore, hHistory⟩ := eval_codeEvaluatorHistoryBeforeCell_exists s q input
  have hFuel := eval_codeEvaluatorCell_fuel s q input
  have hIndex := eval_codeEvaluatorCell_index s q input
  have hTag : Semiformula.Evalb ((5 : M) :> v)
      (code (codePartrecTag (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)))) := by
    simpa only [q, tag_compIndex] using tag_value _ q v hIndex
  have hLeft : Semiformula.Evalb (f :> v)
      (code (codePartrecPayload₁ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)))) := by
    simpa only [q, payload_compIndex, pi₁_pair] using payload1_value _ q v hIndex
  have hRight : Semiformula.Evalb (g :> v)
      (code (codePartrecPayload₂ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)))) := by
    simpa only [q, payload_compIndex, pi₂_pair] using payload2_value _ q v hIndex
  have hRowG : ⟪s, g⟫ < ⟪s, q⟫ := pair_lt_pair_right s (compIndex_right_lt f g)
  have hRowF : ⟪s, f⟫ < ⟪s, q⟫ := pair_lt_pair_right s (compIndex_left_lt f g)
  have hInput : Semiformula.Evalb (input :> v) (code (Code.proj (2 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have hInner (middle : M) :
      Semiformula.Evalb ((middle + 1) :> v)
        (code (codeTableLookup codeEvaluatorHistoryBeforeCell
          (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
          (codePartrecPayload₂ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)))
          (Code.proj (2 : Fin 3)))) ↔
        evalnGraphFormula.val.Evalb ![middle + 1, s, g, input] :=
    prefix_lookup_iff _ _ _ _ ⟪s, q⟫ H s g input (middle + 1) v hHistory hRowG
      hBefore hFuel hRight hInput
  have hOuter (middle : M) :
      Semiformula.Evalb ((output + 1) :> middle :> v)
        (code (codeTableLookup (codeLift codeEvaluatorHistoryBeforeCell)
          (codeLift (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell)))
          (codeLift (codePartrecPayload₁ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell))))
          (codeHead (n := 3)))) ↔
        evalnGraphFormula.val.Evalb ![output + 1, s, f, middle] :=
    prefix_lookup_iff _ _ _ _ ⟪s, q⟫ H s f middle (output + 1) (middle :> v) hHistory hRowF
      ((eval_codeLift_iff _ _ _ _).mpr hBefore)
      ((eval_codeLift_iff _ _ _ _).mpr hFuel)
      ((eval_codeLift_iff _ _ _ _).mpr hLeft) ((eval_codeHead_iff _ _).mpr rfl)
  constructor
  · intro h
    obtain ⟨_, hCell⟩ := (eval_codeHistoryEvaluator_succ_iff_cell s q input output).mp h
    obtain ⟨middle, hI, hO⟩ :=
      eval_codeEvaluatorCell_succ_of_tag_five _ _ output v hTag hCell
    exact ⟨middle, (hInner middle).mp hI, (hOuter middle).mp hO⟩
  · rintro ⟨middle, hI, hO⟩
    have hInputBound : input < s :=
      ((eval_codeHistoryEvaluator_succ_iff_cell s g input middle).mp hI).1
    have hPos : 0 < s := lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le input) hInputBound
    have hBranch := (eval_codeCompEvaluatorCell_succ_iff _ _ _ _ _ output v).mpr
      ⟨middle, (hInner middle).mpr hI, (hOuter middle).mpr hO⟩
    have hCell := build_comp_cell _ _ H input s (output + 1) v hBefore hInput
      hFuel hPos hTag hBranch
    exact (eval_codeHistoryEvaluator_succ_iff_cell s q input output).mpr ⟨hInputBound, hCell⟩

end Models
end CategoricalEssentialIncompleteness.V46.UniformTrace
