/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeInternalGraphs

/-!
# Correctness of the internal native checker

The ten-case rule computation is compared with Foundation's derivation
predicate under an exact hypothesis about the preceding history entries.
Definable induction then establishes that hypothesis for tables of every
internal length in a PA model.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeInternalCorrectness

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeContextMP
open FailureOfComposition.NativeSubstitution
open FailureOfComposition.NativeInternalSyntax
open FailureOfComposition.NativeInternalChecker
open FailureOfComposition.NativeInternalGraphs

private theorem child_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {S : ArithmeticTheory} [S.Δ₁] {h d c s : V}
    (ih : ∀ i < d, historyAccept h i ↔ Derivation S i)
    (hc : c < d) :
    (fstIdx c = s ∧ historyAccept h c) ↔ DerivationOf S c s := by
  rw [ih c hc]
  rfl

/-- The history hypothesis ranges over all internal codes below the current
code; theory agreement is used only at a valid axiom leaf. -/
theorem ruleAccept_iff_derivation
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} {S : ArithmeticTheory} [S.Δ₁]
    (hS : TheoryAxiomAgreement (V := V) A S) (h d : V)
    (ih : ∀ i < d, historyAccept h i ↔ Derivation S i) :
    ruleAccept A h d ↔ Derivation S d := by
  constructor
  · rintro ⟨hs, H⟩
    rcases H with
      (⟨s, _, p, _, rfl, hp, hps, hnps⟩ |
       ⟨s, _, rfl, hv⟩ |
       ⟨s, _, p, _, q, _, dp, hdp, dq, hdq, rfl, hpq, hpD, hqD⟩ |
       ⟨s, _, p, _, q, _, dc, hc, rfl, hpq, he, hh⟩ |
       ⟨s, _, p, _, dc, hc, rfl, hp, hps, he, hh⟩ |
       ⟨s, _, p, _, t, _, dc, hc, rfl, hp, ht, hps, he, hh⟩ |
       ⟨s, _, dc, hc, rfl, hsub, hh⟩ |
       ⟨s, _, dc, hc, rfl, he, hh⟩ |
       ⟨s, _, p, _, d₁, hd₁, d₂, hd₂, rfl, hp, h₁, h₂⟩ |
       ⟨s, _, p, _, rfl, hps, hax⟩)
    · have hseq : IsFormulaSet ℒₒᵣ s := by simpa using hs
      rw [guardedNegValue_eq_neg hp] at hnps
      exact Derivation.axL hseq hps hnps
    · exact Derivation.verumIntro (by simpa using hs) hv
    · exact Derivation.andIntro hpq
        ((child_iff ih hdp).mp hpD) ((child_iff ih hdq).mp hqD)
    · exact Derivation.orIntro hpq ((child_iff ih hc).mp ⟨he, hh⟩)
    · have hseq : IsFormulaSet ℒₒᵣ s := by simpa using hs
      rw [formulaFreeValue_eq_free hp, sequentShiftValue_eq_setShift hseq] at he
      exact Derivation.allIntro hps ((child_iff ih hc).mp ⟨he, hh⟩)
    · rw [subst1Value_eq_substs1 ht hp] at he
      exact Derivation.exsIntro hps ht ((child_iff ih hc).mp ⟨he, hh⟩)
    · have hd := (ih dc hc).mp hh
      exact Derivation.wkRule (by simpa using hs) hsub ⟨rfl, hd⟩
    · have hd := (ih dc hc).mp hh
      rw [sequentShiftValue_eq_setShift hd.isFormulaSet] at he
      have hout := Derivation.shiftRule (show DerivationOf S dc (fstIdx dc) from ⟨rfl, hd⟩)
      rw [← he] at hout
      exact hout
    · rw [guardedNegValue_eq_neg hp] at h₂
      exact Derivation.cutRule ((child_iff ih hd₁).mp h₁) ((child_iff ih hd₂).mp h₂)
    · have hseq : IsFormulaSet ℒₒᵣ s := by simpa using hs
      exact Derivation.axm hseq hps ((hS p (hseq p hps)).mp hax)
  · intro hd
    rcases hd.case with ⟨hs, H⟩
    refine ⟨hs, ?_⟩
    rcases H with
      (⟨s, p, rfl, hp, hnp⟩ | ⟨s, rfl, hv⟩ |
       ⟨s, p, q, dp, dq, rfl, hpq, hdp, hdq⟩ |
       ⟨s, p, q, dc, rfl, hpq, hdc⟩ |
       ⟨s, p, dc, rfl, hp, hdc⟩ |
       ⟨s, p, t, dc, rfl, hp, ht, hdc⟩ |
       ⟨s, dc, rfl, hsub, hdc⟩ | ⟨s, dc, rfl, he, hdc⟩ |
       ⟨s, p, d₁, d₂, rfl, hd₁, hd₂⟩ | ⟨s, p, rfl, hp, hSp⟩)
    · have hseq : IsFormulaSet ℒₒᵣ s := by simpa using hs
      have hfp := hseq p hp
      left
      exact ⟨s, by simp, p, by simp, rfl, hfp, hp,
        by simpa [guardedNegValue_eq_neg hfp] using hnp⟩
    · right; left
      exact ⟨s, by simp, rfl, hv⟩
    · right; right; left
      exact ⟨s, by simp, p, by simp, q, by simp, dp, by simp, dq, by simp,
        rfl, hpq, (child_iff ih (by simp)).mpr hdp, (child_iff ih (by simp)).mpr hdq⟩
    · right; right; right; left
      exact ⟨s, by simp, p, by simp, q, by simp, dc, by simp, rfl, hpq,
        (child_iff ih (by simp)).mpr hdc⟩
    · have hseq : IsFormulaSet ℒₒᵣ s := by simpa using hs
      have hbody : IsSemiformula ℒₒᵣ 1 p := by simpa using hseq _ hp
      right; right; right; right; left
      refine ⟨s, by simp, p, by simp, dc, by simp, rfl, hbody, hp, ?_⟩
      rw [formulaFreeValue_eq_free hbody, sequentShiftValue_eq_setShift hseq]
      exact (child_iff ih (by simp)).mpr hdc
    · have hseq : IsFormulaSet ℒₒᵣ s := by simpa using hs
      have hbody : IsSemiformula ℒₒᵣ 1 p := by simpa using hseq _ hp
      right; right; right; right; right; left
      refine ⟨s, by simp, p, by simp, t, by simp, dc, by simp,
        rfl, hbody, ht, hp, ?_⟩
      rw [subst1Value_eq_substs1 ht hbody]
      exact (child_iff ih (by simp)).mpr hdc
    · right; right; right; right; right; right; left
      exact ⟨s, by simp, dc, by simp, rfl, hsub, (ih dc (by simp)).mpr hdc⟩
    · right; right; right; right; right; right; right; left
      exact ⟨s, by simp, dc, by simp, rfl,
        he.trans (sequentShiftValue_eq_setShift hdc.isFormulaSet).symm,
        (ih dc (by simp)).mpr hdc⟩
    · have hfp : IsFormula ℒₒᵣ p := hd₁.isFormulaSet _ (by simp)
      right; right; right; right; right; right; right; right; left
      refine ⟨s, by simp, p, by simp, d₁, by simp, d₂, by simp, rfl, hfp,
        (child_iff ih (by simp)).mpr hd₁, ?_⟩
      rw [guardedNegValue_eq_neg hfp]
      exact (child_iff ih (by simp)).mpr hd₂
    · have hseq : IsFormulaSet ℒₒᵣ s := by simpa using hs
      right; right; right; right; right; right; right; right; right
      exact ⟨s, by simp, p, by simp, rfl, hp, (hS p (hseq p hp)).mpr hSp⟩

/-- Every preceding entry of every internally generated table recognizes
the actual Foundation derivation predicate. -/
theorem checkTableValue_history_correct
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    {S : ArithmeticTheory} [S.Δ₁] (hS : TheoryAxiomAgreement (V := V) A S)
    (n : V) : ∀ i < n,
    historyAccept (checkTableValue hA n) i ↔ Derivation S i := by
  induction n using ISigma1.sigma1_succ_induction
  · unfold historyAccept
    definability
  case zero => simp
  case succ n ih =>
    intro i hi
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with (hi | he)
    · unfold historyAccept
      rw [checkTableValue_lookup_lt hA hi]
      exact ih i hi
    · subst i
      unfold historyAccept
      rw [checkTableValue_lookup_last]
      have hr := ruleAccept_iff_derivation hS (checkTableValue hA n) n ih
      by_cases hd : Derivation S n <;> simp [ruleCheckValue, hr, hd]

theorem nativeDerivationCheckValue_accepts_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    {S : ArithmeticTheory} [S.Δ₁] (hS : TheoryAxiomAgreement (V := V) A S)
    (d : V) : nativeDerivationCheckValue hA d = 1 ↔ Derivation S d :=
  checkTableValue_history_correct hA hS (d + 1) d (by simp)

/-- Exact acceptance and rejection for all internal proof codes. -/
theorem nativeDerivationCheckGraph_correct
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    {S : ArithmeticTheory} [S.Δ₁] (hS : TheoryAxiomAgreement (V := V) A S)
    (b d : V) :
    Semiformula.Evalb (M := V) ![b, d] (nativeDerivationCheckGraph A).val ↔
      (b = 1 ∧ Derivation S d) ∨ (b = 0 ∧ ¬Derivation S d) := by
  rw [nativeDerivationCheckGraph_iff hA]
  have hiff := nativeDerivationCheckValue_accepts_iff hA hS d
  rcases nativeDerivationCheckValue_isBit hA d with (h0 | h1) <;> simp_all

/-- The sequent argument ranges over the entire model, with no validity
premise. -/
theorem nativeDerivationOfCheckGraph_correct
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    {S : ArithmeticTheory} [S.Δ₁] (hS : TheoryAxiomAgreement (V := V) A S)
    (b d s : V) :
    Semiformula.Evalb (M := V) ![b, d, s] (nativeDerivationOfCheckGraph A).val ↔
      (b = 1 ∧ DerivationOf S d s) ∨ (b = 0 ∧ ¬DerivationOf S d s) := by
  rw [nativeDerivationOfCheckGraph_iff hA]
  have hh : (nativeDerivationCheckValue hA d = 1 ∧ fstIdx d = s) ↔
      DerivationOf S d s := by
    rw [nativeDerivationCheckValue_accepts_iff hA hS]
    exact and_comm
  unfold nativeDerivationOfCheckValue
  rw [hh]
  by_cases hd : DerivationOf S d s <;> simp [hd]

theorem nativeProofCheckGraph_correct
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {A : 𝚺₁.Semisentence 2} (hA : ComputationalAxiomGraph (V := V) A)
    {S : ArithmeticTheory} [S.Δ₁] (hS : TheoryAxiomAgreement (V := V) A S)
    (b d a : V) :
    Semiformula.Evalb (M := V) ![b, d, a] (nativeProofCheckGraph A).val ↔
      (b = 1 ∧ Proof S d a) ∨ (b = 0 ∧ ¬Proof S d a) := by
  simpa [nativeProofCheckGraph, singleton_eq_insert, emptyset_def, Proof] using
    (nativeDerivationOfCheckGraph_correct hA hS b d (insert a 0))

end FailureOfComposition.NativeInternalCorrectness
