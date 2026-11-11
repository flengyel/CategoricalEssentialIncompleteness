/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRefill

/-! # Successful typed stack consumption preserves every underlying stack tail -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance : DecidableEq M := Classical.decEq M

/-- An atomic recursive position consumes its existing top block, never
an element of a subsequently supplied underlying stack. -/
theorem refillLeaf_frame (formula : Bool) (s st u rest tail : M)
    (h : refillLeaf formula s st = adjoin u rest) :
    refillLeaf formula s (Words.append st tail) = adjoin u (Words.append rest tail) := by
  rcases nil_or_adjoin st with rfl | ⟨block, st, rfl⟩
  · simp [refillLeaf] at h
  · by_cases hs : s = 0
    · by_cases hk : π₂ block = (if formula then 1 else 0)
      · have hh : adjoin (π₁ block) st = adjoin u rest := by
          simpa [refillLeaf, hs, hk] using h
        obtain ⟨hu, hr⟩ := (adjoin_inj _ _ _ _).mp hh
        rw [← hu, ← hr]
        simp [refillLeaf, hs, hk]
      · simp [refillLeaf, hs, hk] at h
    · simp [refillLeaf, hs] at h

/-- This is the stack framing property of the actual parser component,
proved by induction on the finite polynomial, with no validity oracle. -/
theorem refill_frame (p : RawPolynomial) (s st u rest tail : M)
    (h : refill p s st = adjoin u rest) :
    refill p s (Words.append st tail) = adjoin u (Words.append rest tail) := by
  induction p generalizing s st u rest tail with
  | term => exact refillLeaf_frame false s st u rest tail h
  | formula => exact refillLeaf_frame true s st u rest tail h
  | coefficient C =>
      have hh : adjoin s st = adjoin u rest := h
      obtain ⟨hu, hr⟩ := (adjoin_inj _ _ _ _).mp hh
      rw [← hu, ← hr]
      rfl
  | unit =>
      by_cases hs : s = 0
      · have hh : adjoin 0 st = adjoin u rest := by simpa [refill, hs] using h
        obtain ⟨hu, hr⟩ := (adjoin_inj _ _ _ _).mp hh
        rw [← hu, ← hr]
        simp [refill, hs]
      · simp [refill, hs] at h
  | product a b ia ib =>
      rcases nil_or_adjoin (refill b (π₂ s) st) with hr | ⟨rv, rs, hr⟩
      · simp [refill, hr] at h
      · rcases nil_or_adjoin (refill a (π₁ s) rs) with hl | ⟨lv, ls, hl⟩
        · simp [refill, hr, hl] at h
        · have hr' := ib (π₂ s) st rv rs tail hr
          have hl' := ia (π₁ s) rs lv ls tail hl
          have hh : adjoin ⟪lv, rv⟫ ls = adjoin u rest := by
            simpa [refill, hr, hl] using h
          obtain ⟨hu, hrest⟩ := (adjoin_inj _ _ _ _).mp hh
          rw [← hu, ← hrest]
          simp [refill, hr', hl']
  | sum a b ia ib =>
      by_cases hk₀ : π₂ s = 0
      · rcases nil_or_adjoin (refill a (π₁ s) st) with hl | ⟨v, rs, hl⟩
        · simp [refill, hk₀, hl] at h
        · have hl' := ia (π₁ s) st v rs tail hl
          have hh : adjoin ⟪v, 0⟫ rs = adjoin u rest := by
            simpa [refill, hk₀, hl] using h
          obtain ⟨hu, hrest⟩ := (adjoin_inj _ _ _ _).mp hh
          rw [← hu, ← hrest]
          simp [refill, hk₀, hl']
      · by_cases hk₁ : π₂ s = 1
        · rcases nil_or_adjoin (refill b (π₁ s) st) with hr | ⟨v, rs, hr⟩
          · simp [refill, hk₁, hr] at h
          · have hr' := ib (π₁ s) st v rs tail hr
            have hh : adjoin ⟪v, 1⟫ rs = adjoin u rest := by
              simpa [refill, hk₁, hr] using h
            obtain ⟨hu, hrest⟩ := (adjoin_inj _ _ _ _).mp hh
            rw [← hu, ← hrest]
            simp [refill, hk₁, hr']
        · simp [refill, hk₀, hk₁] at h

/-- Successful consumption reconstructs exactly the given finite tag and
exactly the consumed stack segment. This is a numerical inverse theorem,
independent of coefficient predicates. -/
theorem refillLeaf_sound (formula : Bool) (s st u rest : M)
    (h : refillLeaf formula s st = adjoin u rest) :
    s = 0 ∧ st = adjoin ⟪u, if formula then 1 else 0⟫ rest := by
  rcases nil_or_adjoin st with rfl | ⟨block, st, rfl⟩
  · simp [refillLeaf] at h
  · by_cases hs : s = 0
    · by_cases hk : π₂ block = (if formula then 1 else 0)
      · have hh : adjoin (π₁ block) st = adjoin u rest := by
          simpa [refillLeaf, hs, hk] using h
        obtain ⟨hu, hr⟩ := (adjoin_inj _ _ _ _).mp hh
        refine ⟨hs, ?_⟩
        rw [← hu, ← hr, ← hk, pair_unpair]
      · simp [refillLeaf, hs, hk] at h
    · simp [refillLeaf, hs] at h

/-- Every successful output of the actual structural parser is the
unique inverse of its root-record shape and ordered child stack. -/
theorem refill_sound (p : RawPolynomial) (s st u rest : M)
    (h : refill p s st = adjoin u rest) :
    shape p u = s ∧ childStack p u rest = st := by
  induction p generalizing s st u rest with
  | term =>
      obtain ⟨hs, hst⟩ := refillLeaf_sound false s st u rest h
      exact ⟨hs.symm, hst.symm⟩
  | formula =>
      obtain ⟨hs, hst⟩ := refillLeaf_sound true s st u rest h
      exact ⟨hs.symm, hst.symm⟩
  | coefficient C =>
      have hh : adjoin s st = adjoin u rest := h
      obtain ⟨hu, hr⟩ := (adjoin_inj _ _ _ _).mp hh
      exact ⟨hu.symm, hr.symm⟩
  | unit =>
      by_cases hs : s = 0
      · have hh : adjoin 0 st = adjoin u rest := by simpa [refill, hs] using h
        obtain ⟨hu, hr⟩ := (adjoin_inj _ _ _ _).mp hh
        exact ⟨hs.symm, hr.symm⟩
      · simp [refill, hs] at h
  | product a b ia ib =>
      rcases nil_or_adjoin (refill b (π₂ s) st) with hr | ⟨rv, rs, hr⟩
      · simp [refill, hr] at h
      · rcases nil_or_adjoin (refill a (π₁ s) rs) with hl | ⟨lv, ls, hl⟩
        · simp [refill, hr, hl] at h
        · have hh : adjoin ⟪lv, rv⟫ ls = adjoin u rest := by
            simpa [refill, hr, hl] using h
          obtain ⟨hu, hrest⟩ := (adjoin_inj _ _ _ _).mp hh
          obtain ⟨hb, hbs⟩ := ib (π₂ s) st rv rs hr
          obtain ⟨ha, has⟩ := ia (π₁ s) rs lv ls hl
          rw [← hu, ← hrest]
          exact ⟨by simp [shape, ha, hb], by simp [childStack, has, hbs]⟩
  | sum a b ia ib =>
      by_cases hk₀ : π₂ s = 0
      · rcases nil_or_adjoin (refill a (π₁ s) st) with hl | ⟨v, rs, hl⟩
        · simp [refill, hk₀, hl] at h
        · have hh : adjoin ⟪v, 0⟫ rs = adjoin u rest := by
            simpa [refill, hk₀, hl] using h
          obtain ⟨hu, hrest⟩ := (adjoin_inj _ _ _ _).mp hh
          obtain ⟨ha, has⟩ := ia (π₁ s) st v rs hl
          rw [← hu, ← hrest]
          exact ⟨by simp [shape, ha, ← hk₀], by simp [childStack, has]⟩
      · by_cases hk₁ : π₂ s = 1
        · rcases nil_or_adjoin (refill b (π₁ s) st) with hr | ⟨v, rs, hr⟩
          · simp [refill, hk₁, hr] at h
          · have hh : adjoin ⟪v, 1⟫ rs = adjoin u rest := by
              simpa [refill, hk₁, hr] using h
            obtain ⟨hu, hrest⟩ := (adjoin_inj _ _ _ _).mp hh
            obtain ⟨hb, hbs⟩ := ib (π₁ s) st v rs hr
            rw [← hu, ← hrest]
            exact ⟨by simp [shape, hb, hk₀, ← hk₁], by simp [childStack, hbs]⟩
        · simp [refill, hk₀, hk₁] at h

@[simp] theorem recordCarrier_eval (a b : RawPolynomial) (record : M) :
    (recordCarrier a b).val.Evalb ![record] ↔
      (π₂ record = 0 ∧ (rawCarrier zeroCarrier zeroCarrier a).val.Evalb ![π₁ record]) ∨
        (π₂ record = 1 ∧ (rawCarrier zeroCarrier zeroCarrier b).val.Evalb ![π₁ record]) := by
  obtain ⟨s, k, rfl⟩ : ∃ s k : M, record = ⟪s, k⟫ :=
    ⟨π₁ record, π₂ record, (pair_unpair record).symm⟩
  simp [recordCarrier]

/-- The actual Sigma-one condition on a typed parser-stack block. -/
def blockCarrier (X Y : Carrier) : Carrier := .mkSigma
  “block. (∃ w, !pairDef.val block w 0 ∧ !X.val w) ∨
    (∃ w, !pairDef.val block w 1 ∧ !Y.val w)”

def stackCarrier (X Y : Carrier) : Carrier :=
  FiniteSigmaOne.finiteMembership (blockCarrier X Y)

@[simp] theorem blockCarrier_eval (X Y : Carrier) (block : M) :
    (blockCarrier X Y).val.Evalb ![block] ↔
      (π₂ block = 0 ∧ X.val.Evalb ![π₁ block]) ∨
        (π₂ block = 1 ∧ Y.val.Evalb ![π₁ block]) := by
  obtain ⟨x, k, rfl⟩ : ∃ x k : M, block = ⟪x, k⟫ :=
    ⟨π₁ block, π₂ block, (pair_unpair block).symm⟩
  simp [blockCarrier]

@[simp] theorem stackCarrier_nil (X Y : Carrier) :
    (stackCarrier X Y).val.Evalb (M := M) ![0] := by
  rw [stackCarrier, ← FiniteSigmaOne.finite_membership_model,
    FiniteSigmaOne.allEntriesCondition_eval]
  simp

@[simp] theorem stackCarrier_adjoin (X Y : Carrier) (block st : M) :
    (stackCarrier X Y).val.Evalb ![adjoin block st] ↔
      (blockCarrier X Y).val.Evalb ![block] ∧ (stackCarrier X Y).val.Evalb ![st] := by
  simp only [stackCarrier, ← FiniteSigmaOne.finite_membership_model,
    FiniteSigmaOne.allEntriesCondition_eval]
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by simp), ?_⟩
    intro i hi
    simpa using h (i + 1) (by simpa using hi)
  · rintro ⟨hb, hs⟩ i hi
    rcases zero_or_succ i with rfl | ⟨j, rfl⟩
    · simpa using hb
    · have hj : j < len st := by simpa using hi
      simpa using hs j hj

/-- Replacing each consumed typed stack block by its numerical child
word reconstructs an element of the actual polynomial source, retaining
all positive coefficient-membership witnesses. -/
theorem refill_typed (X Y : Carrier) (p : RawPolynomial) (s st u rest : M)
    (hs : (rawCarrier zeroCarrier zeroCarrier p).val.Evalb ![s])
    (hst : (stackCarrier X Y).val.Evalb ![st])
    (h : refill p s st = adjoin u rest) :
    (rawCarrier X Y p).val.Evalb ![u] ∧ (stackCarrier X Y).val.Evalb ![rest] := by
  induction p generalizing s st u rest with
  | term =>
      obtain ⟨_, he⟩ := refillLeaf_sound false s st u rest h
      rw [he, stackCarrier_adjoin] at hst
      exact ⟨by simpa [rawCarrier] using hst.1, hst.2⟩
  | formula =>
      obtain ⟨_, he⟩ := refillLeaf_sound true s st u rest h
      rw [he, stackCarrier_adjoin] at hst
      exact ⟨by simpa [rawCarrier] using hst.1, hst.2⟩
  | coefficient C =>
      have hh : adjoin s st = adjoin u rest := h
      obtain ⟨hu, hr⟩ := (adjoin_inj _ _ _ _).mp hh
      exact ⟨by simpa [rawCarrier, ← hu] using hs, by simpa [← hr] using hst⟩
  | unit =>
      by_cases hz : s = 0
      · have hh : adjoin 0 st = adjoin u rest := by simpa [refill, hz] using h
        obtain ⟨hu, hr⟩ := (adjoin_inj _ _ _ _).mp hh
        exact ⟨by simp [rawCarrier, ← hu], by simpa [← hr] using hst⟩
      · simp [refill, hz] at h
  | product a b ia ib =>
      obtain ⟨x, y, rfl, hx, hy⟩ :=
        (rawCarrier_product_eval zeroCarrier zeroCarrier a b s).mp hs
      rcases nil_or_adjoin (refill b y st) with hr | ⟨rv, rs, hr⟩
      · simp [refill, hr] at h
      · rcases nil_or_adjoin (refill a x rs) with hl | ⟨lv, ls, hl⟩
        · simp [refill, hr, hl] at h
        · have hh : adjoin ⟪lv, rv⟫ ls = adjoin u rest := by
            simpa [refill, hr, hl] using h
          obtain ⟨hu, hrest⟩ := (adjoin_inj _ _ _ _).mp hh
          obtain ⟨hrv, hrs⟩ := ib y st rv rs hy hst hr
          obtain ⟨hlv, hls⟩ := ia x rs lv ls hx hrs hl
          rw [← hu, ← hrest]
          exact ⟨(rawCarrier_product_eval X Y a b _).mpr ⟨lv, rv, rfl, hlv, hrv⟩, hls⟩
  | sum a b ia ib =>
      rcases (rawCarrier_sum_eval zeroCarrier zeroCarrier a b s).mp hs with
        ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩
      · rcases nil_or_adjoin (refill a x st) with hl | ⟨v, rs, hl⟩
        · simp [refill, hl] at h
        · have hh : adjoin ⟪v, 0⟫ rs = adjoin u rest := by simpa [refill, hl] using h
          obtain ⟨hu, hrest⟩ := (adjoin_inj _ _ _ _).mp hh
          obtain ⟨hv, hrs⟩ := ia x st v rs hx hst hl
          rw [← hu, ← hrest]
          exact ⟨(rawCarrier_sum_eval X Y a b _).mpr (Or.inl ⟨v, rfl, hv⟩), hrs⟩
      · rcases nil_or_adjoin (refill b y st) with hr | ⟨v, rs, hr⟩
        · simp [refill, hr] at h
        · have hh : adjoin ⟪v, 1⟫ rs = adjoin u rest := by simpa [refill, hr] using h
          obtain ⟨hu, hrest⟩ := (adjoin_inj _ _ _ _).mp hh
          obtain ⟨hv, hrs⟩ := ib y st v rs hy hst hr
          rw [← hu, ← hrest]
          exact ⟨(rawCarrier_sum_eval X Y a b _).mpr (Or.inr ⟨v, rfl, hv⟩), hrs⟩

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
