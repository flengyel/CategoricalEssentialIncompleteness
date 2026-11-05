/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRefillLaws

/-! # Positive fiber conditions and one graph-defined postfix evaluation step -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open Coding

/-- A value block records its actual value and its term/formula sort.
The parameter projection is a positive graph assertion. -/
def fiberBlockGraph (P X Y : Carrier) (ξ υ : Graph) : 𝚺₁.Semisentence 2 := .mkSigma
  “p block. (∃ x, !pairDef.val block x 0 ∧ !P.val p ∧ !X.val x ∧ !ξ.val x p) ∨
    (∃ y, !pairDef.val block y 1 ∧ !P.val p ∧ !Y.val y ∧ !υ.val y p)”

/-- Boundedly many positive witnesses suffice even when the stack has
nonstandard length. No decision procedure for a fiber is assumed. -/
def fiberStackGraph (P X Y : Carrier) (ξ υ : Graph) : 𝚺₁.Semisentence 2 :=
  let B := fiberBlockGraph P X Y ξ υ
  .mkSigma “p stack. ∃ l, !lenDef.val l stack ∧
    ∀ i < l, ∃ block, !nthDef.val block stack i ∧ !B.val p block”

/-- Zero is an error status, and stack+1 is a successful value-stack
status. Both cases remain in the same supplied parameter fiber. -/
def statusGraph (P X Y : Carrier) (ξ υ : Graph) : 𝚺₁.Semisentence 2 :=
  let S := fiberStackGraph P X Y ξ υ
  .mkSigma “p status. !P.val p ∧
    (status = 0 ∨ ∃ stack, status = stack + 1 ∧ !S.val p stack)”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (P X Y : Carrier) (ξ υ : Graph)

@[simp] theorem fiberBlockGraph_eval (p block : M) :
    (fiberBlockGraph P X Y ξ υ).val.Evalb ![p, block] ↔
      (π₂ block = 0 ∧ (rawFiber P X Y ξ υ .term).val.Evalb ![p, π₁ block]) ∨
        (π₂ block = 1 ∧ (rawFiber P X Y ξ υ .formula).val.Evalb ![p, π₁ block]) := by
  obtain ⟨x, k, rfl⟩ : ∃ x k : M, block = ⟪x, k⟫ :=
    ⟨π₁ block, π₂ block, (pair_unpair block).symm⟩
  simp [fiberBlockGraph, rawFiber]

@[simp] theorem fiberStackGraph_eval (p stack : M) :
    (fiberStackGraph P X Y ξ υ).val.Evalb ![p, stack] ↔
      ∀ i < len stack, (fiberBlockGraph P X Y ξ υ).val.Evalb ![p, nth stack i] := by
  simp [fiberStackGraph]

@[simp] theorem fiberStackGraph_nil (p : M) :
    (fiberStackGraph P X Y ξ υ).val.Evalb ![p, (0 : M)] := by
  simp

@[simp] theorem fiberStackGraph_adjoin (p block stack : M) :
    (fiberStackGraph P X Y ξ υ).val.Evalb ![p, adjoin block stack] ↔
      (fiberBlockGraph P X Y ξ υ).val.Evalb ![p, block] ∧
        (fiberStackGraph P X Y ξ υ).val.Evalb ![p, stack] := by
  simp only [fiberStackGraph_eval]
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by simp), ?_⟩
    intro i hi
    simpa using h (i + 1) (by simpa using hi)
  · rintro ⟨hb, hs⟩ i hi
    rcases zero_or_succ i with rfl | ⟨j, rfl⟩
    · simpa using hb
    · have hj : j < len stack := by simpa using hi
      simpa using hs j hj

/-- Structural success supplies exactly the fiber premise required by
an arbitrary graph-defined root operation. Only the record's positive
coefficient condition and the existing value-stack fibers are used. -/
theorem refill_fiber (q : RawPolynomial) (p s stack u rest : M)
    (hp : P.val.Evalb ![p])
    (hs : (rawCarrier zeroCarrier zeroCarrier q).val.Evalb ![s])
    (hst : (fiberStackGraph P X Y ξ υ).val.Evalb ![p, stack])
    (h : refill q s stack = adjoin u rest) :
    (rawFiber P X Y ξ υ q).val.Evalb ![p, u] ∧
      (fiberStackGraph P X Y ξ υ).val.Evalb ![p, rest] := by
  induction q generalizing s stack u rest with
  | term =>
      obtain ⟨_, he⟩ := refillLeaf_sound false s stack u rest h
      rw [he, fiberStackGraph_adjoin] at hst
      exact ⟨by simpa using hst.1, hst.2⟩
  | formula =>
      obtain ⟨_, he⟩ := refillLeaf_sound true s stack u rest h
      rw [he, fiberStackGraph_adjoin] at hst
      exact ⟨by simpa using hst.1, hst.2⟩
  | coefficient C =>
      have hh : adjoin s stack = adjoin u rest := h
      obtain ⟨hu, hr⟩ := (adjoin_inj _ _ _ _).mp hh
      exact ⟨by simpa [rawFiber, rawCarrier, ← hu] using And.intro hp hs,
        by simpa [← hr] using hst⟩
  | unit =>
      by_cases hz : s = 0
      · have hh : adjoin 0 stack = adjoin u rest := by simpa [refill, hz] using h
        obtain ⟨hu, hr⟩ := (adjoin_inj _ _ _ _).mp hh
        exact ⟨by simp [rawFiber, ← hu, hp], by simpa [← hr] using hst⟩
      · simp [refill, hz] at h
  | product a b ia ib =>
      obtain ⟨x, y, rfl, hx, hy⟩ :=
        (rawCarrier_product_eval zeroCarrier zeroCarrier a b s).mp hs
      rcases nil_or_adjoin (refill b y stack) with hr | ⟨rv, rs, hr⟩
      · simp [refill, hr] at h
      · rcases nil_or_adjoin (refill a x rs) with hl | ⟨lv, ls, hl⟩
        · simp [refill, hr, hl] at h
        · have hh : adjoin ⟪lv, rv⟫ ls = adjoin u rest := by
            simpa [refill, hr, hl] using h
          obtain ⟨hu, hrest⟩ := (adjoin_inj _ _ _ _).mp hh
          obtain ⟨hrv, hrs⟩ := ib y stack rv rs hy hst hr
          obtain ⟨hlv, hls⟩ := ia x rs lv ls hx hrs hl
          rw [← hu, ← hrest]
          exact ⟨(rawFiber_product_eval P X Y ξ υ a b p _).mpr
            ⟨lv, rv, rfl, hlv, hrv⟩, hls⟩
  | sum a b ia ib =>
      rcases (rawCarrier_sum_eval zeroCarrier zeroCarrier a b s).mp hs with
        ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩
      · rcases nil_or_adjoin (refill a x stack) with hl | ⟨v, rs, hl⟩
        · simp [refill, hl] at h
        · have hh : adjoin ⟪v, 0⟫ rs = adjoin u rest := by simpa [refill, hl] using h
          obtain ⟨hu, hrest⟩ := (adjoin_inj _ _ _ _).mp hh
          obtain ⟨hv, hrs⟩ := ia x stack v rs hx hst hl
          rw [← hu, ← hrest]
          exact ⟨(rawFiber_sum_eval P X Y ξ υ a b p _).mpr (Or.inl ⟨v, rfl, hv⟩), hrs⟩
      · rcases nil_or_adjoin (refill b y stack) with hr | ⟨v, rs, hr⟩
        · simp [refill, hr] at h
        · have hh : adjoin ⟪v, 1⟫ rs = adjoin u rest := by simpa [refill, hr] using h
          obtain ⟨hu, hrest⟩ := (adjoin_inj _ _ _ _).mp hh
          obtain ⟨hv, hrs⟩ := ib y stack v rs hy hst hr
          rw [← hu, ← hrest]
          exact ⟨(rawFiber_sum_eval P X Y ξ υ a b p _).mpr (Or.inr ⟨v, rfl, hv⟩), hrs⟩

@[simp] theorem statusGraph_eval (p status : M) :
    (statusGraph P X Y ξ υ).val.Evalb ![p, status] ↔
      P.val.Evalb ![p] ∧ (status = 0 ∨
        (fiberStackGraph P X Y ξ υ).val.Evalb ![p, status - 1]) := by
  have he : (statusGraph P X Y ξ υ).val.Evalb ![p, status] ↔
      P.val.Evalb ![p] ∧ (status = 0 ∨ ∃ stack : M,
        status = stack + 1 ∧ (fiberStackGraph P X Y ξ υ).val.Evalb ![p, stack]) := by
    simp [statusGraph]
  rw [he]
  constructor
  · rintro ⟨hp, hz | ⟨stack, hst, hs⟩⟩
    · exact ⟨hp, Or.inl hz⟩
    · exact ⟨hp, Or.inr (by simpa [hst] using hs)⟩
  · rintro ⟨hp, hz | hs⟩
    · exact ⟨hp, Or.inl hz⟩
    · rcases zero_or_succ status with hz | ⟨stack, hst⟩
      · exact ⟨hp, Or.inl hz⟩
      · exact ⟨hp, Or.inr ⟨stack, hst, by simpa [hst] using hs⟩⟩

end Models

namespace SliceAlgebra
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)

/-- The partiality test uses only structural zero/sort/stack tests.
A successful root operation contributes all of its actual Sigma-one
computation trace through the positive occurrence of termOp/formulaOp. -/
def valueStepGraph : 𝚺₁.Semisentence 4 :=
  let S := statusGraph P X Y A.termProjection.graph A.formulaProjection.graph
  let R := recordCarrier a b
  let L := refillGraph a
  let F := refillGraph b
  let G := A.termOp
  let H := A.formulaOp
  .mkSigma “p record old new. !R.val record ∧ !S.val p old ∧ !S.val p new ∧
    ((old = 0 ∧ new = 0) ∨
      (∃ s stack l, !pairDef.val record s 0 ∧ old = stack + 1 ∧ !L.val l s stack ∧
        ((l = 0 ∧ new = 0) ∨ ∃ u rest value block next,
          !adjoinDef.val l u rest ∧ !G.val p u value ∧
          !pairDef.val block value 0 ∧ !adjoinDef.val next block rest ∧ new = next + 1)) ∨
      (∃ s stack r, !pairDef.val record s 1 ∧ old = stack + 1 ∧ !F.val r s stack ∧
        ((r = 0 ∧ new = 0) ∨ ∃ u rest value block next,
          !adjoinDef.val r u rest ∧ !H.val p u value ∧
          !pairDef.val block value 1 ∧ !adjoinDef.val next block rest ∧ new = next + 1)))”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* T]

/-- An executable numerical structural test is followed, on success,
by the actual given graph operation. -/
def StepOutcome (formula : Bool) (p s stack new : M) : Prop :=
  let q := if formula then b else a
  let op := if formula then A.formulaOp else A.termOp
  (refill q s stack = 0 ∧ new = 0) ∨ ∃ u rest value : M,
    refill q s stack = adjoin u rest ∧ op.val.Evalb ![p, u, value] ∧
      new = adjoin ⟪value, if formula then 1 else 0⟫ rest + 1

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem valueStepGraph_eval (p record old new : M) :
    A.valueStepGraph.val.Evalb ![p, record, old, new] ↔
      (recordCarrier a b).val.Evalb ![record] ∧
      (statusGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, old] ∧
      (statusGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, new] ∧
      ((old = 0 ∧ new = 0) ∨
        (∃ s stack : M, record = ⟪s, 0⟫ ∧ old = stack + 1 ∧
          A.StepOutcome false p s stack new) ∨
        (∃ s stack : M, record = ⟪s, 1⟫ ∧ old = stack + 1 ∧
          A.StepOutcome true p s stack new)) := by
  simp [valueStepGraph, StepOutcome]

/-- Operation traces give the next state's fiber positively. -/
theorem stepOutcome_exists (formula : Bool) (p s stack : M)
    (hp : P.val.Evalb ![p])
    (hs : (rawCarrier zeroCarrier zeroCarrier (if formula then b else a)).val.Evalb ![s])
    (hst : (fiberStackGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, stack]) :
    ∃ new : M, A.StepOutcome formula p s stack new ∧
      (statusGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, new] := by
  rcases nil_or_adjoin (refill (if formula then b else a) s stack) with hz | ⟨u, rest, hu⟩
  · exact ⟨0, Or.inl ⟨hz, rfl⟩, by simp [hp]⟩
  · obtain ⟨hf, hr⟩ := refill_fiber P X Y A.termProjection.graph A.formulaProjection.graph
      (if formula then b else a) p s stack u rest hp hs hst hu
    cases formula
    · obtain ⟨value, hv, _⟩ := A.term_total_model p u hf
      obtain ⟨_, hvf⟩ := A.term_support_model p u value hv
      refine ⟨adjoin ⟪value, 0⟫ rest + 1, Or.inr ⟨u, rest, value, hu, hv, rfl⟩, ?_⟩
      exact (statusGraph_eval P X Y A.termProjection.graph A.formulaProjection.graph p _).mpr
        ⟨hp, Or.inr (by simpa [hvf.1, hvf.2, hp, hr] using
          (fiberStackGraph_adjoin P X Y A.termProjection.graph A.formulaProjection.graph
            p ⟪value, 0⟫ rest).mpr ⟨by simp [rawFiber, hp, hvf.1, hvf.2], hr⟩)⟩
    · obtain ⟨value, hv, _⟩ := A.formula_total_model p u hf
      obtain ⟨_, hvf⟩ := A.formula_support_model p u value hv
      refine ⟨adjoin ⟪value, 1⟫ rest + 1, Or.inr ⟨u, rest, value, hu, hv, rfl⟩, ?_⟩
      exact (statusGraph_eval P X Y A.termProjection.graph A.formulaProjection.graph p _).mpr
        ⟨hp, Or.inr (by simpa [hvf.1, hvf.2, hp, hr] using
          (fiberStackGraph_adjoin P X Y A.termProjection.graph A.formulaProjection.graph
            p ⟪value, 1⟫ rest).mpr ⟨by simp [rawFiber, hp, hvf.1, hvf.2], hr⟩)⟩

theorem stepOutcome_unique (formula : Bool) (p s stack y z : M)
    (hy : A.StepOutcome formula p s stack y) (hz : A.StepOutcome formula p s stack z) : y = z := by
  rcases hy with ⟨hy, rfl⟩ | ⟨u, rest, value, hu, hv, rfl⟩
  · rcases hz with ⟨_, rfl⟩ | ⟨u, rest, value, hu, _, _⟩
    · rfl
    · simp [hy] at hu
  · rcases hz with ⟨hz, rfl⟩ | ⟨u', rest', value', hu', hv', rfl⟩
    · simp [hz] at hu
    · have hh : adjoin u rest = adjoin u' rest' := hu.symm.trans hu'
      obtain ⟨huu, hrr⟩ := (adjoin_inj _ _ _ _).mp hh
      subst u'
      subst rest'
      have he : value = value' := by
        cases formula
        · exact A.term_functional_model p u value value' hv hv'
        · exact A.formula_functional_model p u value value' hv hv'
      rw [he]

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem valueStepGraph_zero (p record new : M) :
    A.valueStepGraph.val.Evalb ![p, record, 0, new] ↔
      (recordCarrier a b).val.Evalb ![record] ∧ P.val.Evalb ![p] ∧ new = 0 := by
  simp [valueStepGraph_eval, and_assoc]
  intro _ _ hnew
  exact Or.inl hnew

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem valueStepGraph_term (p s stack new : M) :
    A.valueStepGraph.val.Evalb ![p, ⟪s, 0⟫, stack + 1, new] ↔
      (rawCarrier zeroCarrier zeroCarrier a).val.Evalb ![s] ∧
      (statusGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, stack + 1] ∧
      (statusGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, new] ∧
      A.StepOutcome false p s stack new := by
  simp [valueStepGraph_eval]

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem valueStepGraph_formula (p s stack new : M) :
    A.valueStepGraph.val.Evalb ![p, ⟪s, 1⟫, stack + 1, new] ↔
      (rawCarrier zeroCarrier zeroCarrier b).val.Evalb ![s] ∧
      (statusGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, stack + 1] ∧
      (statusGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, new] ∧
      A.StepOutcome true p s stack new := by
  simp [valueStepGraph_eval]

/-- Every coefficient-valid constructor record acts totally on the
error-or-typed-stack carrier. A failure is purely structural. -/
theorem valueStep_existsUnique (p record old : M)
    (hrecord : (recordCarrier a b).val.Evalb ![record])
    (hold : (statusGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, old]) :
    ∃! new : M, A.valueStepGraph.val.Evalb ![p, record, old, new] := by
  have hp := (statusGraph_eval P X Y A.termProjection.graph A.formulaProjection.graph p old).mp hold |>.1
  rcases zero_or_succ old with rfl | ⟨stack, rfl⟩
  · refine ⟨0, (A.valueStepGraph_zero p record 0).mpr ⟨hrecord, hp, rfl⟩, ?_⟩
    intro z hz
    exact ((A.valueStepGraph_zero p record z).mp hz).2.2
  · have hst : (fiberStackGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, stack] := by
      simpa using ((statusGraph_eval P X Y A.termProjection.graph A.formulaProjection.graph
        p (stack + 1)).mp hold).2
    obtain ⟨s, k, rfl⟩ : ∃ s k : M, record = ⟪s, k⟫ :=
      ⟨π₁ record, π₂ record, (pair_unpair record).symm⟩
    rcases (recordCarrier_eval a b ⟪s, k⟫).mp hrecord with ⟨hk, hs⟩ | ⟨hk, hs⟩
    · have hk' : k = 0 := by simpa using hk
      subst k
      obtain ⟨new, hnew, hnf⟩ := A.stepOutcome_exists false p s stack hp (by simpa using hs) hst
      refine ⟨new, (A.valueStepGraph_term p s stack new).mpr ⟨by simpa using hs, hold, hnf, hnew⟩, ?_⟩
      intro z hz
      exact A.stepOutcome_unique false p s stack z new
        ((A.valueStepGraph_term p s stack z).mp hz).2.2.2 hnew
    · have hk' : k = 1 := by simpa using hk
      subst k
      obtain ⟨new, hnew, hnf⟩ := A.stepOutcome_exists true p s stack hp (by simpa using hs) hst
      refine ⟨new, (A.valueStepGraph_formula p s stack new).mpr ⟨by simpa using hs, hold, hnf, hnew⟩, ?_⟩
      intro z hz
      exact A.stepOutcome_unique true p s stack z new
        ((A.valueStepGraph_formula p s stack z).mp hz).2.2.2 hnew

end Models
end SliceAlgebra
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
