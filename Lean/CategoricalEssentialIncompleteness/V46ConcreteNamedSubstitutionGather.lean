/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPrimitiveParser

/-! Numeric collection of recursive-leaf lists in the exact ordered
polynomial chart. Coefficient and unit entries contribute the empty list. -/

@[expose] public section
noncomputable section
local instance primitiveNamedGatherDecidableEqNat : DecidableEq ℕ := Classical.decEq ℕ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
open SyntacticSyntax SyntacticSyntax.Coding

def gatherGraph : RawPolynomial → 𝚺₁.Semisentence 2
  | .term => .mkSigma “out value. out = value”
  | .formula => .mkSigma “out value. out = value”
  | .coefficient _ => .mkSigma “out value. out = 0”
  | .unit => .mkSigma “out value. out = 0”
  | .product a b =>
    let A := gatherGraph a
    let B := gatherGraph b
    .mkSigma “out value. ∃ l r x y, !pi₁Def.val l value ∧ !pi₂Def.val r value ∧
      !A.val x l ∧ !B.val y r ∧ !Words.appendDef.val out x y”
  | .sum a b =>
    let A := gatherGraph a
    let B := gatherGraph b
    .mkSigma “out value. ∃ tag payload, !pi₁Def.val payload value ∧ !pi₂Def.val tag value ∧
      ((tag = 0 ∧ !A.val out payload) ∨ (tag ≠ 0 ∧ !B.val out payload))”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance primitiveNamedGatherModelDecidableEq : DecidableEq M := Classical.decEq M

def gather : RawPolynomial → M → M
  | .term, value => value
  | .formula, value => value
  | .coefficient _, _ => 0
  | .unit, _ => 0
  | .product a b, value => Words.append (gather a (π₁ value)) (gather b (π₂ value))
  | .sum a b, value => if π₂ value = 0 then gather a (π₁ value) else gather b (π₁ value)

@[simp] theorem gatherGraph_eval (q : RawPolynomial) (out value : M) :
    (gatherGraph q).val.Evalb ![out,value] ↔ out = gather q value := by
  induction q generalizing out value with
  | term => simp [gatherGraph, gather]
  | formula => simp [gatherGraph, gather]
  | coefficient _ => simp [gatherGraph, gather]
  | unit => simp [gatherGraph, gather]
  | product a b ia ib => simp [gatherGraph, gather, ia, ib]
  | sum a b ia ib =>
      by_cases h : π₂ value = 0 <;> simp [gatherGraph, gather, ia, ib, h]

instance gather_defined (q : RawPolynomial) :
    𝚺₁-Function₁ (gather q : M → M) via gatherGraph q := .mk fun v => by
  have hv : ![v 0,v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa [hv] using gatherGraph_eval q (v 0) (v 1)
instance gather_definable (q : RawPolynomial) : 𝚺₁-Function₁ (gather q : M → M) :=
  (gather_defined q).to_definable

end Models

open SyntacticSyntax.NatVectors

theorem gather_primrec (q : RawPolynomial) : Primrec (gather q : ℕ → ℕ) := by
  induction q with
  | term => exact Primrec.id
  | formula => exact Primrec.id
  | coefficient _ => exact Primrec.const 0
  | unit => exact Primrec.const 0
  | product a b ia ib => exact append_primrec.comp (ia.comp pi1_primrec) (ib.comp pi2_primrec)
  | sum a b ia ib =>
      exact Primrec.ite (Primrec.eq.comp pi2_primrec (Primrec.const 0))
        (ia.comp pi1_primrec) (ib.comp pi1_primrec)

end CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
