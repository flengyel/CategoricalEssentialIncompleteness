/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46UniformTraceHalving

/-! # Actual program-index decoding on arbitrary internal indices

Division and remainder below are the model's arithmetic operations. Their
relationship to the literal Code decoder follows from internal halving,
not from agreement on external standard numerals.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.ProgramIndices
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance decoderLocalInstance1 : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance decoderLocalInstance2 : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 :=
  models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance decoderLocalInstance3 : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  models_of_subtheory (U := 𝗜𝚺 1) inferInstance
local instance decoderLocalInstance4 : DecidableEq M := Classical.decEq M
local instance decoderLocalInstance5 : DecidableLT M := Classical.decRel _

noncomputable def payload (q : M) : M := (q - 4) / 4

noncomputable def tag (q : M) : M :=
  if q < 4 then q else 4 + 2 * ((q - 4) % 2) + ((q - 4) / 2) % 2

noncomputable def pairIndex (f g : M) : M := 4 + 4 * ⟪f, g⟫
noncomputable def compIndex (f g : M) : M := 4 + 4 * ⟪f, g⟫ + 2
noncomputable def precIndex (f g : M) : M := 4 + 4 * ⟪f, g⟫ + 1
noncomputable def rfindIndex (f : M) : M := 4 + 4 * f + 3

theorem payload_value {n : ℕ} (A : Code n) (q : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (q :> v) (code A)) :
    Semiformula.Evalb (payload q :> v) (code (codePartrecPayload A)) := by
  have hc : Semiformula.Evalb ((4 : M) :> v) (code (codeConst (n := n) 4)) :=
    (eval_codeConst_iff _ _ _).mpr (by simp)
  have hs := eval_codeSub A (codeConst 4) q 4 v hA hc
  have hh := half_value (codeSub A (codeConst 4)) (q - 4) v hs
  have hh' := half_value (codeDiv2 (codeSub A (codeConst 4))) ((q - 4) / 2) v hh
  have he : (q - 4) / 4 = (q - 4) / 2 / 2 := by
    simpa only [show (2 : M) * 2 = 4 by norm_num] using div_mul (q - 4) (2 : M) 2
  simpa only [payload, he, codePartrecPayload] using hh'

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem lt_value {n : ℕ} (A B : Code n) (a b : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (a :> v) (code A))
    (hB : Semiformula.Evalb (b :> v) (code B)) :
    Semiformula.Evalb ((if a < b then 1 else 0) :> v) (code (codeLt A B)) := by
  apply (eval_codeLt_iff _ _ _ _).mpr
  refine ⟨a, b, hA, hB, ?_⟩
  by_cases h : a < b
  · exact Or.inl ⟨h, ite_eq_left h⟩
  · exact Or.inr ⟨h, ite_eq_right h⟩

theorem tag_value {n : ℕ} (A : Code n) (q : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (q :> v) (code A)) :
    Semiformula.Evalb (tag q :> v) (code (codePartrecTag A)) := by
  have hc (k : ℕ) : Semiformula.Evalb ((k : M) :> v) (code (codeConst (n := n) k)) :=
    (eval_codeConst_iff _ _ _).mpr (by simp)
  have hshift := eval_codeSub A (codeConst 4) q 4 v hA (hc 4)
  have hb := eval_codeRem _ _ (q - 4) 2 v hshift (hc 2)
  have hh := half_value _ (q - 4) v hshift
  have hbh := eval_codeRem _ _ ((q - 4) / 2) 2 v hh (hc 2)
  have hmul := (eval_codeMul_iff _ _ _ _).mpr ⟨2, (q - 4) % 2, hc 2, hb, rfl⟩
  have hadd := (eval_codeAdd_iff _ _ _ _).mpr ⟨4, 2 * ((q - 4) % 2), hc 4, hmul, rfl⟩
  have hout := (eval_codeAdd_iff _ _ _ _).mpr
    ⟨4 + 2 * ((q - 4) % 2), ((q - 4) / 2) % 2, hadd, hbh, rfl⟩
  have htest := lt_value A (codeConst 4) q 4 v hA (hc 4)
  by_cases hq : q < 4
  · simp only [ite_eq_left hq] at htest
    simpa only [tag, ite_eq_left hq, codePartrecTag, codeBodd] using
      eval_codeIfPos_of _ _ _ 1 q _ q v htest hA hout (Or.inl ⟨by simp, rfl⟩)
  · simp only [ite_eq_right hq] at htest
    simpa only [tag, ite_eq_right hq, codePartrecTag, codeBodd] using
      eval_codeIfPos_of _ _ _ 0 q _ _ v htest hA hout (Or.inr ⟨rfl, rfl⟩)

theorem payload1_value {n : ℕ} (A : Code n) (q : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (q :> v) (code A)) :
    Semiformula.Evalb (π₁ (payload q) :> v) (code (codePartrecPayload₁ A)) :=
  eval_codeUnpair₁ _ (payload q) v (payload_value A q v hA)

theorem payload2_value {n : ℕ} (A : Code n) (q : M) (v : Fin n → M)
    (hA : Semiformula.Evalb (q :> v) (code A)) :
    Semiformula.Evalb (π₂ (payload q) :> v) (code (codePartrecPayload₂ A)) :=
  eval_codeUnpair₂ _ (payload q) v (payload_value A q v hA)

private theorem shift_four (p delta : M) :
    (4 + 4 * p + delta) - 4 = 4 * p + delta := by
  rw [add_assoc, add_comm (4 : M) (4 * p + delta), add_sub_self]

@[simp] theorem payload_pairIndex (f g : M) : payload (pairIndex f g) = ⟪f, g⟫ := by
  have hs : pairIndex f g - 4 = 4 * ⟪f, g⟫ := by simp [pairIndex]
  simpa only [payload, hs, add_zero] using
    div_mul_add' ⟪f, g⟫ (4 : M) (r := 0) (by norm_num)

@[simp] theorem payload_compIndex (f g : M) : payload (compIndex f g) = ⟪f, g⟫ := by
  have hs : compIndex f g - 4 = 4 * ⟪f, g⟫ + 2 := by
    exact shift_four ⟪f, g⟫ 2
  simpa only [payload, hs] using div_mul_add' ⟪f, g⟫ (4 : M) (r := 2) (by norm_num)

@[simp] theorem payload_precIndex (f g : M) : payload (precIndex f g) = ⟪f, g⟫ := by
  have hs : precIndex f g - 4 = 4 * ⟪f, g⟫ + 1 := by
    exact shift_four ⟪f, g⟫ 1
  simpa only [payload, hs] using div_mul_add' ⟪f, g⟫ (4 : M) (r := 1) (by norm_num)

@[simp] theorem payload_rfindIndex (f : M) : payload (rfindIndex f) = f := by
  have hs : rfindIndex f - 4 = 4 * f + 3 := by
    exact shift_four f 3
  simpa only [payload, hs] using div_mul_add' f (4 : M) (r := 3) (by norm_num)

@[simp] theorem tag_pairIndex (f g : M) : tag (pairIndex f g) = 4 := by
  have hn : ¬pairIndex f g < 4 := by simp [pairIndex]
  have hs : pairIndex f g - 4 = 4 * ⟪f, g⟫ := by simp [pairIndex]
  have he : (4 : M) * ⟪f, g⟫ = 2 * (2 * ⟪f, g⟫) := by
    simp only [← mul_assoc]
    norm_num
  norm_num [tag, hn, hs, he]

@[simp] theorem tag_compIndex (f g : M) : tag (compIndex f g) = 5 := by
  have hn : ¬compIndex f g < 4 := by simp [compIndex]
  have hs : compIndex f g - 4 = 4 * ⟪f, g⟫ + 2 := by
    exact shift_four ⟪f, g⟫ 2
  have he : (4 : M) * ⟪f, g⟫ + 2 = 2 * (2 * ⟪f, g⟫ + 1) := by
    simp only [mul_add, mul_one, ← mul_assoc]
    norm_num
  norm_num [tag, hn, hs, he]

@[simp] theorem tag_precIndex (f g : M) : tag (precIndex f g) = 6 := by
  have hn : ¬precIndex f g < 4 := by simp [precIndex]
  have hs : precIndex f g - 4 = 4 * ⟪f, g⟫ + 1 := by
    exact shift_four ⟪f, g⟫ 1
  have he : (4 : M) * ⟪f, g⟫ + 1 = 2 * (2 * ⟪f, g⟫) + 1 := by
    simp only [← mul_assoc]
    norm_num
  norm_num [tag, hn, hs, he, div_mul_add_self']

@[simp] theorem tag_rfindIndex (f : M) : tag (rfindIndex f) = 7 := by
  have hn : ¬rfindIndex f < 4 := by simp [rfindIndex]
  have hs : rfindIndex f - 4 = 4 * f + 3 := by
    exact shift_four f 3
  have he : (4 : M) * f + 3 = 2 * (2 * f + 1) + 1 := by
    simp only [mul_add, mul_one, ← mul_assoc, add_assoc]
    norm_num
  norm_num [tag, hn, hs, he, div_mul_add_self']

end Models
end CategoricalEssentialIncompleteness.V46.UniformTrace.ProgramIndices
