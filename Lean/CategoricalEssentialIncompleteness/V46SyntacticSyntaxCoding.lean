/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRaw
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxWords

/-! # Constructor records and ordered child blocks for literal postfix syntax -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

/-- Recursive positions are erased to zero in a root record; coefficient
labels, finite constructor tags and fixed unit padding are retained. -/
def shapeGraph : RawPolynomial → 𝚺₁.Semisentence 2
  | .term => .mkSigma “o u. o = 0”
  | .formula => .mkSigma “o u. o = 0”
  | .coefficient _ => .mkSigma “o u. o = u”
  | .unit => .mkSigma “o u. o = 0”
  | .product a b =>
      let A := shapeGraph a
      let B := shapeGraph b
      .mkSigma “o u. ∃ x y s t, !pairDef.val u x y ∧
        !A.val s x ∧ !B.val t y ∧ !pairDef.val o s t”
  | .sum a b =>
      let A := shapeGraph a
      let B := shapeGraph b
      .mkSigma “o u. ∃ x k s, !pairDef.val u x k ∧
        ((k = 0 ∧ !A.val s x) ∨ (k ≠ 0 ∧ !B.val s x)) ∧ !pairDef.val o s k”

/-- Recursive leaves contribute their entire child words. Coefficient
and unit positions contribute no records. Products retain left-to-right order. -/
def childrenWordGraph : RawPolynomial → 𝚺₁.Semisentence 2
  | .term => .mkSigma “o u. o = u”
  | .formula => .mkSigma “o u. o = u”
  | .coefficient _ => .mkSigma “o u. o = 0”
  | .unit => .mkSigma “o u. o = 0”
  | .product a b =>
      let A := childrenWordGraph a
      let B := childrenWordGraph b
      .mkSigma “o u. ∃ x y s t, !pairDef.val u x y ∧ !A.val s x ∧
        !B.val t y ∧ !Words.appendDef.val o s t”
  | .sum a b =>
      let A := childrenWordGraph a
      let B := childrenWordGraph b
      .mkSigma “o u. ∃ x k, !pairDef.val u x k ∧
        ((k = 0 ∧ !A.val o x) ∨ (k ≠ 0 ∧ !B.val o x))”

def zeroCarrier : Carrier := .mkSigma “x. x = 0”

/-- A constructor record carries precisely a finite constructor tag and
its coefficient labels. There is no child pointer or membership witness. -/
def recordCarrier (a b : RawPolynomial) : Carrier :=
  let A := rawCarrier zeroCarrier zeroCarrier a
  let B := rawCarrier zeroCarrier zeroCarrier b
  .mkSigma “r. (∃ s, !pairDef.val r s 0 ∧ !A.val s) ∨
    (∃ s, !pairDef.val r s 1 ∧ !B.val s)”

def coefficients (a b : RawPolynomial) : Carrier :=
  FiniteSigmaOne.finiteMembership (recordCarrier a b)

/-- Appending the root record is literal postfix construction. -/
def constructorGraph (formula : Bool) (p : RawPolynomial) : 𝚺₁.Semisentence 2 :=
  let S := shapeGraph p
  let W := childrenWordGraph p
  match formula with
  | false => .mkSigma “o u. ∃ s w r, !S.val s u ∧ !W.val w u ∧
      !pairDef.val r s 0 ∧ !concatDef.val o w r”
  | true => .mkSigma “o u. ∃ s w r, !S.val s u ∧ !W.val w u ∧
      !pairDef.val r s 1 ∧ !concatDef.val o w r”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance : DecidableEq M := Classical.decEq M

noncomputable def shape : RawPolynomial → M → M
  | .term, _ => 0
  | .formula, _ => 0
  | .coefficient _, u => u
  | .unit, _ => 0
  | .product a b, u => ⟪shape a (π₁ u), shape b (π₂ u)⟫
  | .sum a b, u => ⟪if π₂ u = 0 then shape a (π₁ u) else shape b (π₁ u), π₂ u⟫

noncomputable def childrenWord : RawPolynomial → M → M
  | .term, u => u
  | .formula, u => u
  | .coefficient _, _ => 0
  | .unit, _ => 0
  | .product a b, u => Words.append (childrenWord a (π₁ u)) (childrenWord b (π₂ u))
  | .sum a b, u => if π₂ u = 0 then childrenWord a (π₁ u) else childrenWord b (π₁ u)

/-- Parsing each child block pushes the last child first on the stack. -/
noncomputable def childStack : RawPolynomial → M → M → M
  | .term, u, s => adjoin ⟪u, 0⟫ s
  | .formula, u, s => adjoin ⟪u, 1⟫ s
  | .coefficient _, _, s => s
  | .unit, _, s => s
  | .product a b, u, s => childStack b (π₂ u) (childStack a (π₁ u) s)
  | .sum a b, u, s => if π₂ u = 0 then childStack a (π₁ u) s else childStack b (π₁ u) s

@[simp] theorem shapeGraph_eval (p : RawPolynomial) (o u : M) :
    (shapeGraph p).val.Evalb ![o, u] ↔ o = shape p u := by
  induction p generalizing o u with
  | term => simp [shapeGraph, shape]
  | formula => simp [shapeGraph, shape]
  | coefficient C => simp [shapeGraph, shape]
  | unit => simp [shapeGraph, shape]
  | product a b ia ib =>
      obtain ⟨x, y, rfl⟩ : ∃ x y : M, u = ⟪x, y⟫ :=
        ⟨π₁ u, π₂ u, (pair_unpair u).symm⟩
      simp [shapeGraph, shape, ia, ib]
  | sum a b ia ib =>
      obtain ⟨x, y, rfl⟩ : ∃ x y : M, u = ⟪x, y⟫ :=
        ⟨π₁ u, π₂ u, (pair_unpair u).symm⟩
      by_cases h : y = 0 <;> simp [shapeGraph, shape, ia, ib, h]

@[simp] theorem childrenWordGraph_eval (p : RawPolynomial) (o u : M) :
    (childrenWordGraph p).val.Evalb ![o, u] ↔ o = childrenWord p u := by
  induction p generalizing o u with
  | term => simp [childrenWordGraph, childrenWord]
  | formula => simp [childrenWordGraph, childrenWord]
  | coefficient C => simp [childrenWordGraph, childrenWord]
  | unit => simp [childrenWordGraph, childrenWord]
  | product a b ia ib =>
      obtain ⟨x, y, rfl⟩ : ∃ x y : M, u = ⟪x, y⟫ :=
        ⟨π₁ u, π₂ u, (pair_unpair u).symm⟩
      simp [childrenWordGraph, childrenWord, ia, ib]
  | sum a b ia ib =>
      obtain ⟨x, y, rfl⟩ : ∃ x y : M, u = ⟪x, y⟫ :=
        ⟨π₁ u, π₂ u, (pair_unpair u).symm⟩
      by_cases h : y = 0 <;> simp [childrenWordGraph, childrenWord, ia, ib,
        h]

instance shape_defined (p : RawPolynomial) : 𝚺₁-Function₁ (shape p : M → M) via shapeGraph p :=
  .mk fun v => by
    have hv : ![v 0, v 1] = v := (Matrix.fun_eq_vec_two v).symm
    simpa [hv] using shapeGraph_eval p (v 0) (v 1)

instance shape_definable (p : RawPolynomial) : 𝚺₁-Function₁ (shape p : M → M) :=
  (shape_defined p).to_definable

instance childrenWord_defined (p : RawPolynomial) :
    𝚺₁-Function₁ (childrenWord p : M → M) via childrenWordGraph p := .mk fun v => by
  have hv : ![v 0, v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa [hv] using childrenWordGraph_eval p (v 0) (v 1)

instance childrenWord_definable (p : RawPolynomial) : 𝚺₁-Function₁ (childrenWord p : M → M) :=
  (childrenWord_defined p).to_definable

noncomputable def constructor (formula : Bool) (p : RawPolynomial) (u : M) : M :=
  concat (childrenWord p u) ⟪shape p u, if formula then 1 else 0⟫

@[simp] theorem constructorGraph_eval (formula : Bool) (p : RawPolynomial) (o u : M) :
    (constructorGraph formula p).val.Evalb ![o, u] ↔ o = constructor formula p u := by
  cases formula <;> simp [constructorGraph, constructor]

@[simp] theorem constructor_length (formula : Bool) (p : RawPolynomial) (u : M) :
    len (constructor formula p u) = len (childrenWord p u) + 1 := by simp [constructor]

@[simp] theorem constructor_ne_zero (formula : Bool) (p : RawPolynomial) (u : M) :
    constructor formula p u ≠ 0 := by
  intro h
  have hl := congrArg len h
  simp at hl

theorem shape_carrier {X Y : Carrier} (p : RawPolynomial) (u : M)
    (h : (rawCarrier X Y p).val.Evalb ![u]) :
    (rawCarrier zeroCarrier zeroCarrier p).val.Evalb ![shape p u] := by
  induction p generalizing u with
  | term => simp [rawCarrier, zeroCarrier, shape]
  | formula => simp [rawCarrier, zeroCarrier, shape]
  | coefficient C => exact h
  | unit => simp [rawCarrier, shape]
  | product a b ia ib =>
      obtain ⟨x, y, rfl, hx, hy⟩ := (rawCarrier_product_eval X Y a b u).mp h
      exact (rawCarrier_product_eval zeroCarrier zeroCarrier a b _).mpr
        ⟨shape a x, shape b y, by simp [shape], ia x hx, ib y hy⟩
  | sum a b ia ib =>
      rcases (rawCarrier_sum_eval X Y a b u).mp h with
        ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩
      · exact (rawCarrier_sum_eval zeroCarrier zeroCarrier a b _).mpr
          (Or.inl ⟨shape a x, by simp [shape], ia x hx⟩)
      · exact (rawCarrier_sum_eval zeroCarrier zeroCarrier a b _).mpr
          (Or.inr ⟨shape b y, by simp [shape], ib y hy⟩)

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
