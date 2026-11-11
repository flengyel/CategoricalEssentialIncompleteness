/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxCoding

/-! # Typed stack consumption for finite polynomial constructor records -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

/-- Zero denotes failure. A nonzero result `adjoin u rest` supplies the
reconstructed polynomial value and the unconsumed stack suffix. -/
def refillLeafGraph (formula : Bool) : 𝚺₁.Semisentence 3 :=
  match formula with
  | false => .mkSigma “o s st. ∃ b w k t,
      !fstIdxDef.val b st ∧ !pi₁Def.val w b ∧ !pi₂Def.val k b ∧ !sndIdxDef.val t st ∧
      ((s = 0 ∧ st ≠ 0 ∧ k = 0 ∧ !adjoinDef.val o w t) ∨
        ((s ≠ 0 ∨ st = 0 ∨ k ≠ 0) ∧ o = 0))”
  | true => .mkSigma “o s st. ∃ b w k t,
      !fstIdxDef.val b st ∧ !pi₁Def.val w b ∧ !pi₂Def.val k b ∧ !sndIdxDef.val t st ∧
      ((s = 0 ∧ st ≠ 0 ∧ k = 1 ∧ !adjoinDef.val o w t) ∨
        ((s ≠ 0 ∨ st = 0 ∨ k ≠ 1) ∧ o = 0))”

def refillGraph : RawPolynomial → 𝚺₁.Semisentence 3
  | .term => refillLeafGraph false
  | .formula => refillLeafGraph true
  | .coefficient _ => .mkSigma “o s st. !adjoinDef.val o s st”
  | .unit => .mkSigma “o s st.
      (s = 0 ∧ !adjoinDef.val o 0 st) ∨ (s ≠ 0 ∧ o = 0)”
  | .product a b =>
      let A := refillGraph a
      let B := refillGraph b
      .mkSigma “o s st. ∃ a b r rv rs l lv ls v,
        !pairDef.val s a b ∧ !B.val r b st ∧
        !fstIdxDef.val rv r ∧ !sndIdxDef.val rs r ∧ !A.val l a rs ∧
        !fstIdxDef.val lv l ∧ !sndIdxDef.val ls l ∧ !pairDef.val v lv rv ∧
        (((r = 0 ∨ l = 0) ∧ o = 0) ∨ (r ≠ 0 ∧ l ≠ 0 ∧ !adjoinDef.val o v ls))”
  | .sum a b =>
      let A := refillGraph a
      let B := refillGraph b
      .mkSigma “o s st. ∃ a k l lv ls r rv rs vl vr,
        !pairDef.val s a k ∧ !A.val l a st ∧ !B.val r a st ∧
        !fstIdxDef.val lv l ∧ !sndIdxDef.val ls l ∧
        !fstIdxDef.val rv r ∧ !sndIdxDef.val rs r ∧
        !pairDef.val vl lv 0 ∧ !pairDef.val vr rv 1 ∧
        ((((k = 0 ∧ l = 0) ∨ (k = 1 ∧ r = 0) ∨ (k ≠ 0 ∧ k ≠ 1)) ∧ o = 0) ∨
          (k = 0 ∧ l ≠ 0 ∧ !adjoinDef.val o vl ls) ∨
          (k = 1 ∧ r ≠ 0 ∧ !adjoinDef.val o vr rs))”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance : DecidableEq M := Classical.decEq M

noncomputable def refillLeaf (formula : Bool) (s st : M) : M :=
  if s = 0 ∧ st ≠ 0 ∧ π₂ (fstIdx st) = (if formula then 1 else 0) then
    adjoin (π₁ (fstIdx st)) (sndIdx st) else 0

noncomputable def refill : RawPolynomial → M → M → M
  | .term, s, st => refillLeaf false s st
  | .formula, s, st => refillLeaf true s st
  | .coefficient _, s, st => adjoin s st
  | .unit, s, st => if s = 0 then adjoin 0 st else 0
  | .product a b, s, st =>
      let r := refill b (π₂ s) st
      let l := refill a (π₁ s) (sndIdx r)
      if r = 0 ∨ l = 0 then 0 else adjoin ⟪fstIdx l, fstIdx r⟫ (sndIdx l)
  | .sum a b, s, st =>
      let l := refill a (π₁ s) st
      let r := refill b (π₁ s) st
      if π₂ s = 0 then
        if l = 0 then 0 else adjoin ⟪fstIdx l, 0⟫ (sndIdx l)
      else if π₂ s = 1 then
        if r = 0 then 0 else adjoin ⟪fstIdx r, 1⟫ (sndIdx r)
      else 0

@[simp] private theorem firstDef_eval (o s : M) :
    fstIdxDef.val.Evalb ![o, s] ↔ o = fstIdx s := fstIdx_defined.iff

@[simp] private theorem restDef_eval (o s : M) :
    sndIdxDef.val.Evalb ![o, s] ↔ o = sndIdx s := sndIdx_defined.iff

@[simp] private theorem leftDef_eval (o s : M) :
    pi₁Def.val.Evalb ![o, s] ↔ o = π₁ s := pi₁_defined.iff

@[simp] private theorem rightDef_eval (o s : M) :
    pi₂Def.val.Evalb ![o, s] ↔ o = π₂ s := pi₂_defined.iff

@[simp] theorem refillLeafGraph_eval (formula : Bool) (o s st : M) :
    (refillLeafGraph formula).val.Evalb ![o, s, st] ↔ o = refillLeaf formula s st := by
  cases formula
  · by_cases hs : s = 0 <;> by_cases ht : st = 0 <;>
      by_cases hk : π₂ (fstIdx st) = 0 <;>
        simp [refillLeafGraph, refillLeaf, hs, ht, hk]
  · by_cases hs : s = 0 <;> by_cases ht : st = 0 <;>
      by_cases hk : π₂ (fstIdx st) = 1 <;>
        simp [refillLeafGraph, refillLeaf, hs, ht, hk]

@[simp] theorem refillGraph_eval (p : RawPolynomial) (o s st : M) :
    (refillGraph p).val.Evalb ![o, s, st] ↔ o = refill p s st := by
  induction p generalizing o s st with
  | term => simp [refillGraph, refill]
  | formula => simp [refillGraph, refill]
  | coefficient C => simp [refillGraph, refill]
  | unit => by_cases hs : s = 0 <;> simp [refillGraph, refill, hs]
  | product a b ia ib =>
      obtain ⟨x, y, rfl⟩ : ∃ x y : M, s = ⟪x, y⟫ :=
        ⟨π₁ s, π₂ s, (pair_unpair s).symm⟩
      by_cases hr : refill b y st = 0 <;>
        by_cases hl : refill a x (sndIdx (refill b y st)) = 0 <;>
          simp_all [refillGraph, refill]
  | sum a b ia ib =>
      obtain ⟨x, k, rfl⟩ : ∃ x k : M, s = ⟪x, k⟫ :=
        ⟨π₁ s, π₂ s, (pair_unpair s).symm⟩
      have hh : (refillGraph (.sum a b)).val.Evalb ![o, ⟪x, k⟫, st] ↔
          ((((k = 0 ∧ refill a x st = 0) ∨ (k = 1 ∧ refill b x st = 0) ∨
            (k ≠ 0 ∧ k ≠ 1)) ∧ o = 0) ∨
            (k = 0 ∧ refill a x st ≠ 0 ∧
              o = adjoin ⟪fstIdx (refill a x st), 0⟫ (sndIdx (refill a x st))) ∨
            (k = 1 ∧ refill b x st ≠ 0 ∧
              o = adjoin ⟪fstIdx (refill b x st), 1⟫ (sndIdx (refill b x st)))) := by
        simp [refillGraph, ia, ib]
      rw [hh]
      simp only [refill, pi₁_pair, pi₂_pair]
      by_cases hk₀ : k = 0 <;> by_cases hk₁ : k = 1 <;>
        by_cases hl : refill a x st = 0 <;> by_cases hr : refill b x st = 0 <;> simp_all

instance refill_defined (p : RawPolynomial) :
    𝚺₁-Function₂ (refill p : M → M → M) via refillGraph p := .mk fun v => by
  have hv : ![v 0, v 1, v 2] = v := (Matrix.fun_eq_vec_three v).symm
  simpa [hv] using refillGraph_eval p (v 0) (v 1) (v 2)

instance refill_definable (p : RawPolynomial) : 𝚺₁-Function₂ (refill p : M → M → M) :=
  (refill_defined p).to_definable

@[simp] theorem refillLeaf_cons_false (w st : M) :
    refillLeaf false 0 (adjoin ⟪w, 0⟫ st) = adjoin w st := by simp [refillLeaf]

@[simp] theorem refillLeaf_cons_true (w st : M) :
    refillLeaf true 0 (adjoin ⟪w, 1⟫ st) = adjoin w st := by simp [refillLeaf]

/-- The parser reconstructs exactly the displayed raw polynomial input.
Products consume the right child before the left child on a postfix stack. -/
theorem refill_shape {X Y : Carrier} (p : RawPolynomial) (u st : M)
    (h : (rawCarrier X Y p).val.Evalb ![u]) :
    refill p (shape p u) (childStack p u st) = adjoin u st := by
  induction p generalizing u st with
  | term => simp [refill, shape, childStack]
  | formula => simp [refill, shape, childStack]
  | coefficient C => rfl
  | unit =>
      have hu : u = 0 := by simpa [rawCarrier] using h
      subst u
      simp [refill, shape, childStack]
  | product a b ia ib =>
      obtain ⟨x, y, rfl, hx, hy⟩ := (rawCarrier_product_eval X Y a b u).mp h
      simp [refill, shape, childStack, ib y (childStack a x st) hy, ia x st hx]
  | sum a b ia ib =>
      rcases (rawCarrier_sum_eval X Y a b u).mp h with
        ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩
      · simp [refill, shape, childStack, ia x st hx]
      · simp [refill, shape, childStack, ib y st hy]

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
