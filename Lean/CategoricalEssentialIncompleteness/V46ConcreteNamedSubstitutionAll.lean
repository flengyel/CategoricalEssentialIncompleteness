/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPrimitiveParser

/-! An actual Boolean conjunction of ordered recursive-leaf tests. -/

@[expose] public section
noncomputable section
local instance primitiveNamedAllDecidableEqNat : DecidableEq ℕ := Classical.decEq ℕ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
open SyntacticSyntax SyntacticSyntax.Coding

def allChildrenGraph (F G : 𝚺₁.Semisentence 2) : RawPolynomial → 𝚺₁.Semisentence 2
  | .term => F
  | .formula => G
  | .coefficient _ => .mkSigma “out value. out = 1”
  | .unit => .mkSigma “out value. out = 1”
  | .product a b =>
    let A := allChildrenGraph F G a
    let B := allChildrenGraph F G b
    .mkSigma “out value. ∃ l r x y, !pi₁Def.val l value ∧ !pi₂Def.val r value ∧
      !A.val x l ∧ !B.val y r ∧
      ((x = 1 ∧ y = 1 ∧ out = 1) ∨ ((x ≠ 1 ∨ y ≠ 1) ∧ out = 0))”
  | .sum a b =>
    let A := allChildrenGraph F G a
    let B := allChildrenGraph F G b
    .mkSigma “out value. ∃ tag payload, !pi₁Def.val payload value ∧ !pi₂Def.val tag value ∧
      ((tag = 0 ∧ !A.val out payload) ∨ (tag ≠ 0 ∧ !B.val out payload))”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance primitiveNamedAllModelDecidableEq : DecidableEq M := Classical.decEq M

def allChildren (f g : M → M) : RawPolynomial → M → M
  | .term,value => f value
  | .formula,value => g value
  | .coefficient _,_ => 1
  | .unit,_ => 1
  | .product a b,value =>
      if allChildren f g a (π₁ value) = 1 ∧ allChildren f g b (π₂ value) = 1 then 1 else 0
  | .sum a b,value => if π₂ value = 0 then allChildren f g a (π₁ value) else allChildren f g b (π₁ value)

variable (F G : 𝚺₁.Semisentence 2) (f g : M → M)
  [𝚺₁-Function₁ f via F] [𝚺₁-Function₁ g via G]

@[simp] theorem allChildrenGraph_eval (q : RawPolynomial) (out value : M) :
    (allChildrenGraph F G q).val.Evalb ![out,value] ↔ out = allChildren f g q value := by
  induction q generalizing out value with
  | term => exact (show 𝚺₁-Function₁ f via F from inferInstance).iff
  | formula => exact (show 𝚺₁-Function₁ g via G from inferInstance).iff
  | coefficient _ => simp [allChildrenGraph,allChildren]
  | unit => simp [allChildrenGraph,allChildren]
  | product a b ia ib =>
      by_cases ha : allChildren f g a (π₁ value) = 1 <;>
      by_cases hb : allChildren f g b (π₂ value) = 1 <;>
        simp [allChildrenGraph,allChildren,ia,ib,ha,hb]
  | sum a b ia ib =>
      by_cases h : π₂ value = 0 <;> simp [allChildrenGraph,allChildren,ia,ib,h]

theorem allChildren_defined (q : RawPolynomial) :
    𝚺₁-Function₁ (allChildren f g q : M → M) via allChildrenGraph F G q := .mk fun v => by
  have hv : ![v 0,v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa [hv] using allChildrenGraph_eval F G f g q (v 0) (v 1)

end Models

open SyntacticSyntax.NatVectors

theorem allChildren_primrec (q : RawPolynomial) (f g : ℕ → ℕ)
    (hf : Primrec f) (hg : Primrec g) : Primrec (allChildren f g q : ℕ → ℕ) := by
  induction q with
  | term => exact hf
  | formula => exact hg
  | coefficient _ => exact Primrec.const 1
  | unit => exact Primrec.const 1
  | product a b ia ib =>
      exact Primrec.ite ((Primrec.eq.comp (ia.comp pi1_primrec) (Primrec.const 1)).and
        (Primrec.eq.comp (ib.comp pi2_primrec) (Primrec.const 1)))
        (Primrec.const 1) (Primrec.const 0)
  | sum a b ia ib =>
      exact Primrec.ite (Primrec.eq.comp pi2_primrec (Primrec.const 0))
        (ia.comp pi1_primrec) (ib.comp pi1_primrec)

end CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
