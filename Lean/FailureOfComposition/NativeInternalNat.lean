/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeInternalGraphs
public import FailureOfComposition.NativeInternalSequence

/-!
# Comparison with the accepted numerical checker

Internal histories encode sequences as finite sets of index-bit pairs.
The comparison below uses this encoding explicitly and requires agreement
with the numerical axiom test only on valid formula codes.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeInternalNat

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeContextMP
open FailureOfComposition.NativeSubstitution
open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeSyntaxShift
open FailureOfComposition.NativeProofChecker
open FailureOfComposition.NativeInternalSyntax
open FailureOfComposition.NativeInternalChecker
open FailureOfComposition.NativeInternalGraphs
open FailureOfComposition.NativeInternalSequence

private noncomputable def ruleCases
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (A : 𝚺₁.Semisentence 2) (h d : V) : Prop :=
  IsFormulaSet ℒₒᵣ (fstIdx d) ∧
  ((∃ s, ∃ p, d = axL s p ∧ IsFormula ℒₒᵣ p ∧
      p ∈ s ∧ guardedNegValue p ∈ s) ∨
   (∃ s, d = verumIntro s ∧ ^⊤ ∈ s) ∨
   (∃ s, ∃ p, ∃ q, ∃ dp, ∃ dq, d = andIntro s p q dp dq ∧ p ^⋏ q ∈ s ∧
      (fstIdx dp = insert p s ∧ historyAccept h dp) ∧
      (fstIdx dq = insert q s ∧ historyAccept h dq)) ∨
   (∃ s, ∃ p, ∃ q, ∃ dc, d = orIntro s p q dc ∧ p ^⋎ q ∈ s ∧
      fstIdx dc = insert p (insert q s) ∧ historyAccept h dc) ∨
   (∃ s, ∃ p, ∃ dc, d = allIntro s p dc ∧ IsSemiformula ℒₒᵣ 1 p ∧
      ^∀ p ∈ s ∧
      fstIdx dc = insert (formulaFreeValue p) (sequentShiftValue s) ∧
      historyAccept h dc) ∨
   (∃ s, ∃ p, ∃ t, ∃ dc, d = exsIntro s p t dc ∧
      IsSemiformula ℒₒᵣ 1 p ∧ IsSemiterm ℒₒᵣ 0 t ∧
      ^∃ p ∈ s ∧ fstIdx dc = insert (subst1Value t p) s ∧
      historyAccept h dc) ∨
   (∃ s, ∃ dc, d = wkRule s dc ∧ fstIdx dc ⊆ s ∧
      historyAccept h dc) ∨
   (∃ s, ∃ dc, d = shiftRule s dc ∧
      s = sequentShiftValue (fstIdx dc) ∧ historyAccept h dc) ∨
   (∃ s, ∃ p, ∃ d₁, ∃ d₂, d = cutRule s p d₁ d₂ ∧ IsFormula ℒₒᵣ p ∧
      (fstIdx d₁ = insert p s ∧ historyAccept h d₁) ∧
      (fstIdx d₂ = insert (guardedNegValue p) s ∧ historyAccept h d₂)) ∨
   (∃ s, ∃ p, d = axm s p ∧ p ∈ s ∧
      Semiformula.Evalb (M := V) ![1, p] A.val))


private theorem ruleAccept_iff_cases
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (A : 𝚺₁.Semisentence 2) (h d : V) :
    ruleAccept A h d ↔ ruleCases A h d := by
  constructor
  · rintro ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with
      (⟨s, _, p, _, rfl, h⟩ |
       ⟨s, _, rfl, h⟩ |
       ⟨s, _, p, _, q, _, dp, _, dq, _, rfl, h⟩ |
       ⟨s, _, p, _, q, _, dc, _, rfl, h⟩ |
       ⟨s, _, p, _, dc, _, rfl, h⟩ |
       ⟨s, _, p, _, t, _, dc, _, rfl, h⟩ |
       ⟨s, _, dc, _, rfl, h⟩ |
       ⟨s, _, dc, _, rfl, h⟩ |
       ⟨s, _, p, _, d₁, _, d₂, _, rfl, h⟩ |
       ⟨s, _, p, _, rfl, h⟩)
    · left
      exact ⟨s, p, rfl, h⟩
    · right; left
      exact ⟨s, rfl, h⟩
    · right; right; left
      exact ⟨s, p, q, dp, dq, rfl, h⟩
    · right; right; right; left
      exact ⟨s, p, q, dc, rfl, h⟩
    · right; right; right; right; left
      exact ⟨s, p, dc, rfl, h⟩
    · right; right; right; right; right; left
      exact ⟨s, p, t, dc, rfl, h⟩
    · right; right; right; right; right; right; left
      exact ⟨s, dc, rfl, h⟩
    · right; right; right; right; right; right; right; left
      exact ⟨s, dc, rfl, h⟩
    · right; right; right; right; right; right; right; right; left
      exact ⟨s, p, d₁, d₂, rfl, h⟩
    · right; right; right; right; right; right; right; right; right
      exact ⟨s, p, rfl, h⟩
  · rintro ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with
      (⟨s, p, rfl, h⟩ |
       ⟨s, rfl, h⟩ |
       ⟨s, p, q, dp, dq, rfl, h⟩ |
       ⟨s, p, q, dc, rfl, h⟩ |
       ⟨s, p, dc, rfl, h⟩ |
       ⟨s, p, t, dc, rfl, h⟩ |
       ⟨s, dc, rfl, h⟩ |
       ⟨s, dc, rfl, h⟩ |
       ⟨s, p, d₁, d₂, rfl, h⟩ |
       ⟨s, p, rfl, h⟩)
    · left
      exact ⟨s, by simp, p, by simp, rfl, h⟩
    · right; left
      exact ⟨s, by simp, rfl, h⟩
    · right; right; left
      exact ⟨s, by simp, p, by simp, q, by simp, dp, by simp, dq, by simp, rfl, h⟩
    · right; right; right; left
      exact ⟨s, by simp, p, by simp, q, by simp, dc, by simp, rfl, h⟩
    · right; right; right; right; left
      exact ⟨s, by simp, p, by simp, dc, by simp, rfl, h⟩
    · right; right; right; right; right; left
      exact ⟨s, by simp, p, by simp, t, by simp, dc, by simp, rfl, h⟩
    · right; right; right; right; right; right; left
      exact ⟨s, by simp, dc, by simp, rfl, h⟩
    · right; right; right; right; right; right; right; left
      exact ⟨s, by simp, dc, by simp, rfl, h⟩
    · right; right; right; right; right; right; right; right; left
      exact ⟨s, by simp, p, by simp, d₁, by simp, d₂, by simp, rfl, h⟩
    · right; right; right; right; right; right; right; right; right
      exact ⟨s, by simp, p, by simp, rfl, h⟩


private theorem ruleBodyCheck_expand (ax : ℕ → Bool) (history : List Bool)
    (s tag u : ℕ) : ruleBodyCheck ax history s tag u =
    let chk := fun (h : List Bool) (d c : ℕ) => h.getD d false && (conclusionCode d == c)
  if tag = 0 then
    formulaCodeValid u && sequentMemCode u s &&
      sequentMemCode (formulaNegTotalCode u) s
  else if tag = 1 then (u == 0) && sequentMemCode (Nat.pair 2 0 + 1) s
  else if tag = 2 then
    let p := u.unpair.1
    let q := u.unpair.2.unpair.1
    let dp := u.unpair.2.unpair.2.unpair.1
    let dq := u.unpair.2.unpair.2.unpair.2
    sequentMemCode (formulaAndCode p q) s &&
      chk history dp (sequentInsertCode p s) &&
      chk history dq (sequentInsertCode q s)
  else if tag = 3 then
    let p := u.unpair.1
    let q := u.unpair.2.unpair.1
    let d := u.unpair.2.unpair.2
    sequentMemCode (formulaOrCode p q) s &&
      chk history d (sequentInsertCode p (sequentInsertCode q s))
  else if tag = 4 then
    let p := u.unpair.1
    let d := u.unpair.2
    formulaBodyCodeValid p && sequentMemCode (formulaAllCode p) s &&
      chk history d
        (sequentInsertCode (formulaFreeCode p) (sequentShiftCode s))
  else if tag = 5 then
    let p := u.unpair.1
    let t := u.unpair.2.unpair.1
    let d := u.unpair.2.unpair.2
    formulaBodyCodeValid p && termCodeValid t &&
      sequentMemCode (formulaExistsCode p) s &&
      chk history d (sequentInsertCode (subst1Code t p) s)
  else if tag = 6 then
    sequentSubsetCode (conclusionCode u) s && history.getD u false
  else if tag = 7 then
    (s == sequentShiftCode (conclusionCode u)) && history.getD u false
  else if tag = 8 then
    let p := u.unpair.1
    let d₁ := u.unpair.2.unpair.1
    let d₂ := u.unpair.2.unpair.2
    formulaCodeValid p &&
      chk history d₁ (sequentInsertCode p s) &&
      chk history d₂ (sequentInsertCode (formulaNegTotalCode p) s)
  else if tag = 9 then sequentMemCode u s && ax u
  else false := by rfl

private theorem guardedNegValue_nat (a : ℕ) :
    guardedNegValue a = formulaNegTotalCode a := by
  by_cases ha : IsFormula ℒₒᵣ a
  · rw [guardedNegValue_eq_neg ha, formulaNegTotalCode_eq_neg ha]
  · simp [guardedNegValue, formulaNegTotalCode_eq_zero ha, ha]

private theorem axiom_accept_nat
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := ℕ) A)
    {ax : ℕ → Bool} (hnum : NumericalAxiomAgreement A ax)
    {a : ℕ} (ha : IsFormula ℒₒᵣ a) :
    Semiformula.Evalb (M := ℕ) ![1, a] A.val ↔ ax a = true := by
  constructor
  · intro h1
    have heq : (1 : ℕ) = boolBit (ax a) :=
      (hA.existsUnique a).unique h1 (hnum a ha)
    cases hb : ax a <;> simp [hb] at heq ⊢
  · intro hb
    simpa [hb] using hnum a ha

private theorem pair_cases (u : ℕ) : ∃ p q, u = Nat.pair p q :=
  ⟨u.unpair.1, u.unpair.2, (Nat.pair_unpair u).symm⟩

@[simp] private theorem pi₁_nat_pair (x y : ℕ) : (π₁ (Nat.pair x y) : ℕ) = x := by
  rw [← nat_pair_eq]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- The comparison simplifies all ten nested constructor cases in one theorem.
theorem ruleAccept_nat_iff
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := ℕ) A)
    {ax : ℕ → Bool} (hnum : NumericalAxiomAgreement A ax)
    (h : ℕ) (history : List Bool)
    (hh : ∀ i, historyAccept h i ↔ history.getD i false = true)
    (d : ℕ) : ruleAccept A h d ↔ ruleCheck ax history d = true := by
  cases d with
  | zero => simp [ruleAccept, ruleCheck]
  | succ e =>
      rcases pair_cases e with ⟨s, z, rfl⟩
      rcases pair_cases z with ⟨tag, u, rfl⟩
      simp only [ruleCheck, conclusionCode, Nat.add_sub_cancel, Nat.unpair_pair,
        Nat.succ_ne_zero, ↓reduceIte]
      rw [ruleBodyCheck_expand]
      dsimp only
      split_ifs with h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
      · subst tag
        simp [-List.getD_eq_getElem?_getD, ruleAccept_iff_cases, ruleCases, Bootstrapping.axL,
          verumIntro, andIntro, orIntro, allIntro, exsIntro, wkRule, shiftRule, cutRule, axm,
          nat_pair_eq, Nat.pair_eq_pair, fstIdx, formulaSetCodeValid_iff,
          formulaCodeValid_iff_isFormula,
          Bool.and_eq_true,
          sequentMemCode_iff,
          qqAnd, qqOr, qqAll, qqExs, qqVerum, guardedNegValue_nat,
          formulaFreeValue_nat, sequentShiftValue_nat, subst1Value_nat,
          show ∀ x s : ℕ, insert x s = sequentInsertCode x s from
            fun x s => nat_insert_eq x s, and_assoc, and_left_comm, and_comm]
      · subst tag
        simp [-List.getD_eq_getElem?_getD, ruleAccept_iff_cases, ruleCases, Bootstrapping.axL,
          verumIntro, andIntro, orIntro, allIntro, exsIntro, wkRule, shiftRule, cutRule, axm,
          nat_pair_eq, Nat.pair_eq_pair, fstIdx, formulaSetCodeValid_iff,
          Bool.and_eq_true, beq_iff_eq,
          sequentMemCode_iff,
          qqAnd, qqOr, qqAll, qqExs, qqVerum, guardedNegValue_nat,
          formulaFreeValue_nat, sequentShiftValue_nat, subst1Value_nat,
          show ∀ x s : ℕ, insert x s = sequentInsertCode x s from
            fun x s => nat_insert_eq x s, and_assoc, and_left_comm, and_comm]
      · subst tag
        rcases pair_cases u with ⟨p, v, rfl⟩
        rcases pair_cases v with ⟨q, w, rfl⟩
        rcases pair_cases w with ⟨dp, dq, rfl⟩
        simp [-List.getD_eq_getElem?_getD, ruleAccept_iff_cases, ruleCases, Bootstrapping.axL,
          verumIntro, andIntro, orIntro, allIntro, exsIntro, wkRule, shiftRule, cutRule, axm,
          nat_pair_eq, Nat.pair_eq_pair, fstIdx, formulaSetCodeValid_iff,
          Bool.and_eq_true, beq_iff_eq,
          sequentMemCode_iff, conclusionCode_eq_fstIdx,
          formulaAndCode,
          qqAnd, qqOr, qqAll, qqExs, qqVerum, guardedNegValue_nat,
          formulaFreeValue_nat, sequentShiftValue_nat, subst1Value_nat,
          show ∀ x s : ℕ, insert x s = sequentInsertCode x s from
            fun x s => nat_insert_eq x s, ← hh, and_assoc, and_left_comm, and_comm]
      · subst tag
        rcases pair_cases u with ⟨p, v, rfl⟩
        rcases pair_cases v with ⟨q, dc, rfl⟩
        simp [-List.getD_eq_getElem?_getD, ruleAccept_iff_cases, ruleCases, Bootstrapping.axL,
          verumIntro, andIntro, orIntro, allIntro, exsIntro, wkRule, shiftRule, cutRule, axm,
          nat_pair_eq, Nat.pair_eq_pair, fstIdx, formulaSetCodeValid_iff,
          Bool.and_eq_true, beq_iff_eq,
          sequentMemCode_iff, conclusionCode_eq_fstIdx,
          formulaOrCode,
          qqAnd, qqOr, qqAll, qqExs, qqVerum, guardedNegValue_nat,
          formulaFreeValue_nat, sequentShiftValue_nat, subst1Value_nat,
          show ∀ x s : ℕ, insert x s = sequentInsertCode x s from
            fun x s => nat_insert_eq x s, ← hh, and_assoc, and_left_comm, and_comm]
      · subst tag
        rcases pair_cases u with ⟨p, dc, rfl⟩
        simp [-List.getD_eq_getElem?_getD, ruleAccept_iff_cases, ruleCases, Bootstrapping.axL,
          verumIntro, andIntro, orIntro, allIntro, exsIntro, wkRule, shiftRule, cutRule, axm,
          nat_pair_eq, Nat.pair_eq_pair, fstIdx, formulaSetCodeValid_iff,
          formulaBodyCodeValid_iff_isSemiformula,
          Bool.and_eq_true, beq_iff_eq,
          sequentMemCode_iff, conclusionCode_eq_fstIdx,
          formulaAllCode,
          qqAnd, qqOr, qqAll, qqExs, qqVerum, guardedNegValue_nat,
          formulaFreeValue_nat, sequentShiftValue_nat, subst1Value_nat,
          show ∀ x s : ℕ, insert x s = sequentInsertCode x s from
            fun x s => nat_insert_eq x s, ← hh, and_assoc, and_left_comm, and_comm]
      · subst tag
        rcases pair_cases u with ⟨p, v, rfl⟩
        rcases pair_cases v with ⟨t, dc, rfl⟩
        simp [-List.getD_eq_getElem?_getD, ruleAccept_iff_cases, ruleCases, Bootstrapping.axL,
          verumIntro, andIntro, orIntro, allIntro, exsIntro, wkRule, shiftRule, cutRule, axm,
          nat_pair_eq, Nat.pair_eq_pair, fstIdx, formulaSetCodeValid_iff,
          formulaBodyCodeValid_iff_isSemiformula,
          termCodeValid_iff_isSemiterm, Bool.and_eq_true, beq_iff_eq,
          sequentMemCode_iff, conclusionCode_eq_fstIdx,
          formulaExistsCode,
          qqAnd, qqOr, qqAll, qqExs, qqVerum, guardedNegValue_nat,
          formulaFreeValue_nat, sequentShiftValue_nat, subst1Value_nat,
          show ∀ x s : ℕ, insert x s = sequentInsertCode x s from
            fun x s => nat_insert_eq x s, ← hh, and_assoc, and_left_comm, and_comm]
      · subst tag
        simp [-List.getD_eq_getElem?_getD, ruleAccept_iff_cases, ruleCases, Bootstrapping.axL,
          verumIntro, andIntro, orIntro, allIntro, exsIntro, wkRule, shiftRule, cutRule, axm,
          nat_pair_eq, Nat.pair_eq_pair, fstIdx, formulaSetCodeValid_iff,
          Bool.and_eq_true,
          sequentSubsetCode_iff, conclusionCode_eq_fstIdx,
          qqAnd, qqOr, qqAll, qqExs, qqVerum, guardedNegValue_nat,
          formulaFreeValue_nat, sequentShiftValue_nat, subst1Value_nat,
          show ∀ x s : ℕ, insert x s = sequentInsertCode x s from
            fun x s => nat_insert_eq x s, ← hh, and_assoc, and_left_comm, and_comm]
      · subst tag
        simp [-List.getD_eq_getElem?_getD, ruleAccept_iff_cases, ruleCases, Bootstrapping.axL,
          verumIntro, andIntro, orIntro, allIntro, exsIntro, wkRule, shiftRule, cutRule, axm,
          nat_pair_eq, Nat.pair_eq_pair, fstIdx, formulaSetCodeValid_iff,
          Bool.and_eq_true, beq_iff_eq,
          conclusionCode_eq_fstIdx,
          qqAnd, qqOr, qqAll, qqExs, qqVerum, guardedNegValue_nat,
          formulaFreeValue_nat, sequentShiftValue_nat, subst1Value_nat,
          show ∀ x s : ℕ, insert x s = sequentInsertCode x s from
            fun x s => nat_insert_eq x s, ← hh, and_assoc, and_left_comm, and_comm]
      · subst tag
        rcases pair_cases u with ⟨p, v, rfl⟩
        rcases pair_cases v with ⟨d₁, d₂, rfl⟩
        simp [-List.getD_eq_getElem?_getD, ruleAccept_iff_cases, ruleCases, Bootstrapping.axL,
          verumIntro, andIntro, orIntro, allIntro, exsIntro, wkRule, shiftRule, cutRule, axm,
          nat_pair_eq, Nat.pair_eq_pair, fstIdx, formulaSetCodeValid_iff,
          formulaCodeValid_iff_isFormula,
          Bool.and_eq_true, beq_iff_eq,
          conclusionCode_eq_fstIdx,
          qqAnd, qqOr, qqAll, qqExs, qqVerum, guardedNegValue_nat,
          formulaFreeValue_nat, sequentShiftValue_nat, subst1Value_nat,
          show ∀ x s : ℕ, insert x s = sequentInsertCode x s from
            fun x s => nat_insert_eq x s, ← hh, and_assoc, and_left_comm, and_comm]
      · subst tag
        by_cases hs : IsFormulaSet ℒₒᵣ s
        · by_cases hu : u ∈ s
          · simp [-List.getD_eq_getElem?_getD, ruleAccept_iff_cases, ruleCases, Bootstrapping.axL,
          verumIntro, andIntro, orIntro, allIntro, exsIntro, wkRule, shiftRule, cutRule, axm,
          nat_pair_eq, Nat.pair_eq_pair, fstIdx, formulaSetCodeValid_iff,
          Bool.and_eq_true,
          sequentMemCode_iff,
          qqAnd, qqOr, qqAll, qqExs, qqVerum, guardedNegValue_nat,
          formulaFreeValue_nat, sequentShiftValue_nat, subst1Value_nat,
          show ∀ x s : ℕ, insert x s = sequentInsertCode x s from
            fun x s => nat_insert_eq x s, and_assoc, and_left_comm, and_comm, hs, hu,
              axiom_accept_nat hA hnum (hs u hu)]
          · simp [-List.getD_eq_getElem?_getD, ruleAccept_iff_cases, ruleCases, Bootstrapping.axL,
          verumIntro, andIntro, orIntro, allIntro, exsIntro, wkRule, shiftRule, cutRule, axm,
          nat_pair_eq, Nat.pair_eq_pair, fstIdx, formulaSetCodeValid_iff,
          Bool.and_eq_true,
          sequentMemCode_iff,
          qqAnd, qqOr, qqAll, qqExs, qqVerum, guardedNegValue_nat,
          formulaFreeValue_nat, sequentShiftValue_nat, subst1Value_nat,
          show ∀ x s : ℕ, insert x s = sequentInsertCode x s from
            fun x s => nat_insert_eq x s, and_assoc, and_left_comm, and_comm, hs, hu]
        · simp [-List.getD_eq_getElem?_getD, ruleAccept_iff_cases, ruleCases, Bootstrapping.axL,
          verumIntro, andIntro, orIntro, allIntro, exsIntro, wkRule, shiftRule, cutRule, axm,
          nat_pair_eq, Nat.pair_eq_pair, fstIdx, formulaSetCodeValid_iff,
          Bool.and_eq_true,
          sequentMemCode_iff,
          qqAnd, qqOr, qqAll, qqExs, qqVerum, guardedNegValue_nat,
          formulaFreeValue_nat, sequentShiftValue_nat, subst1Value_nat,
          show ∀ x s : ℕ, insert x s = sequentInsertCode x s from
            fun x s => nat_insert_eq x s, and_assoc, and_left_comm, and_comm, hs]
      · simp [-List.getD_eq_getElem?_getD, ruleAccept_iff_cases, ruleCases, Bootstrapping.axL,
          verumIntro, andIntro, orIntro, allIntro, exsIntro, wkRule, shiftRule, cutRule, axm,
          nat_pair_eq, Nat.pair_eq_pair, fstIdx,
          qqAnd, qqOr, qqAll, qqExs, qqVerum, guardedNegValue_nat,
          formulaFreeValue_nat, sequentShiftValue_nat, subst1Value_nat,
          show ∀ x s : ℕ, insert x s = sequentInsertCode x s from
            fun x s => nat_insert_eq x s, and_assoc, and_left_comm, and_comm,
          h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉]

theorem ruleCheckValue_nat
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := ℕ) A)
    {ax : ℕ → Bool} (hnum : NumericalAxiomAgreement A ax)
    (h : ℕ) (history : List Bool)
    (hh : ∀ i, historyAccept h i ↔ history.getD i false = true)
    (d : ℕ) : ruleCheckValue A h d = boolBit (ruleCheck ax history d) := by
  unfold ruleCheckValue
  rw [ruleAccept_nat_iff hA hnum h history hh d]
  cases ruleCheck ax history d <;> simp

/-- The internally generated HFS sequence is exactly the encoding of the
accepted program's list, for every natural length. -/
theorem checkTableValue_nat
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := ℕ) A)
    {ax : ℕ → Bool} (hnum : NumericalAxiomAgreement A ax) (n : ℕ) :
    checkTableValue hA n = historyCode (checkTable ax n) := by
  induction n with
  | zero => rw [checkTableValue_zero]; rfl
  | succ n ih =>
      rw [checkTableValue_succ, checkTable, historyCode_append, ih]
      rw [ruleCheckValue_nat hA hnum _ _ (historyCode_accepts_iff _) n]

theorem nativeDerivationCheckGraph_nat_iff
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := ℕ) A)
    {ax : ℕ → Bool} (hnum : NumericalAxiomAgreement A ax) (b d : ℕ) :
    Semiformula.Evalb (M := ℕ) ![b, d] (nativeDerivationCheckGraph A).val ↔
      b = boolBit (nativeDerivationCheck ax d) := by
  rw [nativeDerivationCheckGraph_iff hA]
  unfold nativeDerivationCheckValue
  rw [checkTableValue_nat hA hnum, historyCode_lookup]
  rfl

theorem nativeDerivationOfCheckGraph_nat_iff
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := ℕ) A)
    {ax : ℕ → Bool} (hnum : NumericalAxiomAgreement A ax) (b d s : ℕ) :
    Semiformula.Evalb (M := ℕ) ![b, d, s] (nativeDerivationOfCheckGraph A).val ↔
      b = boolBit (nativeDerivationOfCheck ax d s) := by
  have hd : nativeDerivationCheckValue hA d = boolBit (nativeDerivationCheck ax d) :=
    (nativeDerivationCheckGraph_nat_iff hA hnum _ d).mp
      ((nativeDerivationCheckGraph_iff hA _ d).mpr rfl)
  rw [nativeDerivationOfCheckGraph_iff hA]
  unfold nativeDerivationOfCheckValue nativeDerivationOfCheck
  rw [hd, conclusionCode_eq_fstIdx]
  cases nativeDerivationCheck ax d <;>
    by_cases hc : fstIdx d = s <;> simp [hc, boolBit]

theorem nativeProofCheckGraph_nat_iff
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := ℕ) A)
    {ax : ℕ → Bool} (hnum : NumericalAxiomAgreement A ax) (b d a : ℕ) :
    Semiformula.Evalb (M := ℕ) ![b, d, a] (nativeProofCheckGraph A).val ↔
      b = boolBit (nativeProofCheck ax d a) := by
  simp [nativeProofCheckGraph, nativeDerivationOfCheckGraph_nat_iff hA hnum,
    nativeProofCheck, show insert a 0 = sequentInsertCode a 0 from nat_insert_eq a 0]

set_option backward.isDefEq.respectTransparency false in
/-- An invalid formula at an axiom leaf is rejected independently of the
supplied axiom test: membership would invalidate the conclusion sequent. -/
theorem invalid_axiom_leaf_rejected (ax : ℕ → Bool) (history : List Bool)
    (s a : ℕ) (ha : ¬IsFormula ℒₒᵣ a) :
    ruleCheck ax history (axm s a) = false := by
  by_cases hs : IsFormulaSet ℒₒᵣ s
  · have hmem : a ∉ s := fun hm => ha (hs a hm)
    simp [ruleCheck, ruleBodyCheck, axm, conclusionCode, nat_pair_eq,
      formulaSetCodeValid_iff, hs, sequentMemCode_iff, hmem]
  · simp [ruleCheck, axm, conclusionCode, nat_pair_eq, formulaSetCodeValid_iff, hs]

end FailureOfComposition.NativeInternalNat
