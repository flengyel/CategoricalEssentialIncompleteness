/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceComposition

/-! # Pairing-stage certificates for arbitrary internal component indices -/

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
local instance pairingLocalInstance1 : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance pairingLocalInstance2 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance pairingLocalInstance3 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance

theorem select_pair_branch {n : ℕ} (A X : Code n) (fuel o : M) (v : Fin n → M)
    (hFuel : Semiformula.Evalb (fuel :> v) (code (codeUnpair₁ (codeListLength A))))
    (hf : 0 < fuel)
    (hTag : Semiformula.Evalb ((4 : M) :> v)
      (code (codePartrecTag (codeUnpair₂ (codeListLength A)))))
    (h : Semiformula.Evalb (o :> v) (code (codeEvaluatorCell A X))) :
    Semiformula.Evalb (o :> v) (code (codePairEvaluatorCell A
      (codeUnpair₁ (codeListLength A))
      (codePartrecPayload₁ (codeUnpair₂ (codeListLength A)))
      (codePartrecPayload₂ (codeUnpair₂ (codeListLength A))) X)) := by
  have h4 : Semiformula.Evalb ((4 : M) :> v) (code (codeConst (n := n) 4)) :=
    (eval_codeConst_iff _ _ _).mpr (by simp)
  let K := codeUnpair₁ (codeListLength A)
  let Q := codeUnpair₂ (codeListLength A)
  let Tag := codePartrecTag Q
  let Left := codePartrecPayload₁ Q
  let Right := codePartrecPayload₂ Q
  let PairBranch := codePairEvaluatorCell A K Left Right X
  let Later := codeIfPos (codeEq Tag (codeConst 5))
    (codeCompEvaluatorCell A K Left Right X)
    (codeIfPos (codeEq Tag (codeConst 6))
      (codePrecEvaluatorCell A (codeSub K (codeConst 1)) Q Left Right X)
      (codeIfPos (codeEq Tag (codeConst 7))
        (codeRfindEvaluatorCell A (codeSub K (codeConst 1)) Q (codePartrecPayload Q) X)
        (codeBaseEvaluatorCell A X)))
  have htest := eq_value Tag (codeConst 4) (4 : M) 4 v hTag h4
  simp only at htest
  have hbig := select_if_positive K
    (codeIfPos (codeEq Tag (codeConst 4)) PairBranch Later) (codeConst 0)
    fuel o v hFuel hf h
  exact select_if_positive (codeEq Tag (codeConst 4)) PairBranch Later
    1 o v htest (by simp) hbig

theorem build_pair_cell {n : ℕ} (A X : Code n) (table input fuel o : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (table :> v) (code A))
    (hX : Semiformula.Evalb (input :> v) (code X))
    (hFuel : Semiformula.Evalb (fuel :> v) (code (codeUnpair₁ (codeListLength A))))
    (hf : 0 < fuel)
    (hTag : Semiformula.Evalb ((4 : M) :> v)
      (code (codePartrecTag (codeUnpair₂ (codeListLength A)))))
    (hBranch : Semiformula.Evalb (o :> v) (code (codePairEvaluatorCell A
      (codeUnpair₁ (codeListLength A))
      (codePartrecPayload₁ (codeUnpair₂ (codeListLength A)))
      (codePartrecPayload₂ (codeUnpair₂ (codeListLength A))) X))) :
    Semiformula.Evalb (o :> v) (code (codeEvaluatorCell A X)) := by
  obtain ⟨z, hz⟩ := eval_codeEvaluatorCell_exists_of_values A X table input v hA hX
  have hb := select_pair_branch A X fuel z v hFuel hf hTag hz
  have he : z = o := eval_unique hb hBranch
  rwa [he] at hz

theorem pairIndex_left_lt (f g : M) : f < pairIndex f g := by
  have hp : ⟪f, g⟫ ≤ 4 * ⟪f, g⟫ := by
    calc
      ⟪f, g⟫ = 1 * ⟪f, g⟫ := by simp
      _ ≤ 4 * ⟪f, g⟫ := mul_le_mul_right (by norm_num : (1 : M) ≤ 4)
  calc
    f ≤ ⟪f, g⟫ := le_pair_left _ _
    _ < ⟪f, g⟫ + 1 := by simp
    _ ≤ 4 * ⟪f, g⟫ + 1 := by
      simpa only [add_comm] using add_le_add_right hp 1
    _ ≤ 4 * ⟪f, g⟫ + 4 := by
      simpa only [add_comm] using
        add_le_add_left (by norm_num : (1 : M) ≤ 4) (4 * ⟪f, g⟫)
    _ = pairIndex f g := by simp [pairIndex, add_comm]

theorem pairIndex_right_lt (f g : M) : g < pairIndex f g := by
  have hp : ⟪f, g⟫ ≤ 4 * ⟪f, g⟫ := by
    calc
      ⟪f, g⟫ = 1 * ⟪f, g⟫ := by simp
      _ ≤ 4 * ⟪f, g⟫ := mul_le_mul_right (by norm_num : (1 : M) ≤ 4)
  calc
    g ≤ ⟪f, g⟫ := le_pair_right _ _
    _ < ⟪f, g⟫ + 1 := by simp
    _ ≤ 4 * ⟪f, g⟫ + 1 := by
      simpa only [add_comm] using add_le_add_right hp 1
    _ ≤ 4 * ⟪f, g⟫ + 4 := by
      simpa only [add_comm] using
        add_le_add_left (by norm_num : (1 : M) ≤ 4) (4 * ⟪f, g⟫)
    _ = pairIndex f g := by simp [pairIndex, add_comm]

theorem pairing_stage_iff (s f g input output : M) :
    evalnGraphFormula.val.Evalb ![output + 1, s, pairIndex f g, input] ↔
      ∃ left right : M, evalnGraphFormula.val.Evalb ![left + 1, s, f, input] ∧
        evalnGraphFormula.val.Evalb ![right + 1, s, g, input] ∧ output = ⟪left, right⟫ := by
  let q := pairIndex f g
  let v : Fin 3 → M := ![s, q, input]
  obtain ⟨H, hBefore, hHistory⟩ := eval_codeEvaluatorHistoryBeforeCell_exists s q input
  have hFuel := eval_codeEvaluatorCell_fuel s q input
  have hIndex := eval_codeEvaluatorCell_index s q input
  have hTag : Semiformula.Evalb ((4 : M) :> v)
      (code (codePartrecTag (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)))) := by
    simpa only [q, tag_pairIndex] using tag_value _ q v hIndex
  have hLeft : Semiformula.Evalb (f :> v)
      (code (codePartrecPayload₁ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)))) := by
    simpa only [q, payload_pairIndex, pi₁_pair] using payload1_value _ q v hIndex
  have hRight : Semiformula.Evalb (g :> v)
      (code (codePartrecPayload₂ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)))) := by
    simpa only [q, payload_pairIndex, pi₂_pair] using payload2_value _ q v hIndex
  have hRowF : ⟪s, f⟫ < ⟪s, q⟫ := pair_lt_pair_right s (pairIndex_left_lt f g)
  have hRowG : ⟪s, g⟫ < ⟪s, q⟫ := pair_lt_pair_right s (pairIndex_right_lt f g)
  have hInput : Semiformula.Evalb (input :> v) (code (Code.proj (2 : Fin 3))) :=
    (eval_proj_iff _ _ _).mpr rfl
  have hFirst (left : M) :
      Semiformula.Evalb ((left + 1) :> v)
        (code (codeTableLookup codeEvaluatorHistoryBeforeCell
          (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell))
          (codePartrecPayload₁ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell)))
          (Code.proj (2 : Fin 3)))) ↔
        evalnGraphFormula.val.Evalb ![left + 1, s, f, input] :=
    prefix_lookup_iff _ _ _ _ ⟪s, q⟫ H s f input (left + 1) v hHistory hRowF
      hBefore hFuel hLeft hInput
  have hSecond (left right : M) :
      Semiformula.Evalb ((right + 1) :> left :> v)
        (code (codeTableLookup (codeLift codeEvaluatorHistoryBeforeCell)
          (codeLift (codeUnpair₁ (codeListLength codeEvaluatorHistoryBeforeCell)))
          (codeLift (codePartrecPayload₂ (codeUnpair₂ (codeListLength codeEvaluatorHistoryBeforeCell))))
          (codeLift (Code.proj (2 : Fin 3))))) ↔
        evalnGraphFormula.val.Evalb ![right + 1, s, g, input] :=
    prefix_lookup_iff _ _ _ _ ⟪s, q⟫ H s g input (right + 1) (left :> v) hHistory hRowG
      ((eval_codeLift_iff _ _ _ _).mpr hBefore)
      ((eval_codeLift_iff _ _ _ _).mpr hFuel)
      ((eval_codeLift_iff _ _ _ _).mpr hRight) ((eval_codeLift_iff _ _ _ _).mpr hInput)
  constructor
  · intro h
    obtain ⟨hInputBound, hCell⟩ := (eval_codeHistoryEvaluator_succ_iff_cell s q input output).mp h
    have hPos : 0 < s := lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le input) hInputBound
    have hPair := select_pair_branch _ _ s (output + 1) v hFuel hPos hTag hCell
    obtain ⟨left, right, hL, hR, hOut⟩ :=
      (eval_codePairEvaluatorCell_succ_iff _ _ _ _ _ output v).mp hPair
    exact ⟨left, right, (hFirst left).mp hL, (hSecond left right).mp hR, hOut⟩
  · rintro ⟨left, right, hL, hR, hOut⟩
    have hInputBound := ((eval_codeHistoryEvaluator_succ_iff_cell s f input left).mp hL).1
    have hPos : 0 < s := lt_of_le_of_lt (FFL.FirstOrder.Arithmetic.zero_le input) hInputBound
    have hBranch := (eval_codePairEvaluatorCell_succ_iff _ _ _ _ _ output v).mpr
      ⟨left, right, (hFirst left).mpr hL, (hSecond left right).mpr hR, hOut⟩
    have hCell := build_pair_cell _ _ H input s (output + 1) v hBefore hInput
      hFuel hPos hTag hBranch
    exact (eval_codeHistoryEvaluator_succ_iff_cell s q input output).mpr ⟨hInputBound, hCell⟩

end Models
end CategoricalEssentialIncompleteness.V46.UniformTrace
