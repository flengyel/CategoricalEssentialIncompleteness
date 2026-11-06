/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonTermRootArithmetic
import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionFreeVariables

/-! # Scalar formula-result cases of the proved named traversal root -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance namedComparisonFormulaRootArithmeticDecidableEq : DecidableEq M := Classical.decEq M

def equalityInput (u : M) : M :=
  Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair u 0) 0) 0) 0
def relationInput (u : M) : M :=
  Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair u 1) 0) 0) 0
def negationInput (u : M) : M := Arithmetic.pair (Arithmetic.pair (Arithmetic.pair u 1) 0) 0
def implicationInput (u : M) : M := Arithmetic.pair (Arithmetic.pair u 1) 0
def quantifierInput (u : M) : M := Arithmetic.pair u 1

theorem allChildren_termPower_one (g : M → M) (n : ℕ) (u : M) :
    ConcreteNamedSubstitution.allChildren (fun _ => 1) g (SyntaxPolynomial.power .term n) u = 1 := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n =>
        simp [SyntaxPolynomial.power,ConcreteNamedSubstitution.allChildren,ih]

theorem allChildren_constructors_one (π : ℕ → Carrier) (g : M → M) (n : ℕ) (u : M) :
    ConcreteNamedSubstitution.allChildren (fun _ => 1) g (SyntaxPolynomial.constructors π n) u = 1 := by
  induction n generalizing u with
  | zero => simp [SyntaxPolynomial.constructors,ConcreteNamedSubstitution.allChildren,allChildren_termPower_one]
  | succ n ih =>
      simp [SyntaxPolynomial.constructors,ConcreteNamedSubstitution.allChildren,ih,allChildren_termPower_one]

theorem formulaRoot_equality_result (V : Carrier) (π : ℕ → Carrier) (d : ℕ) (param u : M) :
    ConcreteNamedSubstitution.result (ConcreteNamedSubstitution.formulaRoot V π d param (equalityInput u)) =
      ConcreteNamedSubstitution.ok (Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
        (equalityInput (ConcreteNamedSubstitution.mapChildren ConcreteNamedSubstitution.result
          ConcreteNamedSubstitution.original (SyntaxPolynomial.power .term 2) u))) := by
  simp [ConcreteNamedSubstitution.formulaRoot,ConcreteNamedSubstitution.result_payload,
    equalityInput,SyntaxPolynomial.formulaExpression,SyntaxPolynomial.power,
    ConcreteNamedSubstitution.allChildren,ConcreteNamedSubstitution.mapChildren]

theorem formulaRoot_relation_result (V : Carrier) (π : ℕ → Carrier) (d : ℕ) (param u : M) :
    ConcreteNamedSubstitution.result (ConcreteNamedSubstitution.formulaRoot V π d param (relationInput u)) =
      ConcreteNamedSubstitution.ok (Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
        (relationInput (ConcreteNamedSubstitution.mapChildren ConcreteNamedSubstitution.result
          ConcreteNamedSubstitution.original (SyntaxPolynomial.constructors π d) u))) := by
  simp only [ConcreteNamedSubstitution.formulaRoot,ConcreteNamedSubstitution.result_payload,
    relationInput,SyntaxPolynomial.formulaExpression,ConcreteNamedSubstitution.allChildren,
    ConcreteNamedSubstitution.mapChildren,pi₁_pair,pi₂_pair,↓reduceIte,
    allChildren_constructors_one,_root_.one_ne_zero]
  rw [termOnly_constructors π ConcreteNamedSubstitution.result ConcreteNamedSubstitution.successfulValue
    ConcreteNamedSubstitution.original d u]

theorem formulaRoot_negation_result (V : Carrier) (π : ℕ → Carrier) (d : ℕ) (param body : M) :
    ConcreteNamedSubstitution.result (ConcreteNamedSubstitution.formulaRoot V π d param (negationInput body)) =
      if π₂ (ConcreteNamedSubstitution.result body) = 1 then
        ConcreteNamedSubstitution.ok (Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
          (negationInput (π₁ (ConcreteNamedSubstitution.result body)))) else 0 := by
  by_cases hs : π₂ (ConcreteNamedSubstitution.result body) = 1 <;>
    simp [ConcreteNamedSubstitution.formulaRoot,ConcreteNamedSubstitution.result_payload,
      negationInput,SyntaxPolynomial.formulaExpression,ConcreteNamedSubstitution.allChildren,
      ConcreteNamedSubstitution.mapChildren,ConcreteNamedSubstitution.success,
      ConcreteNamedSubstitution.successfulValue,hs]

theorem formulaRoot_implication_result (V : Carrier) (π : ℕ → Carrier) (d : ℕ) (param children : M) :
    ConcreteNamedSubstitution.result (ConcreteNamedSubstitution.formulaRoot V π d param (implicationInput children)) =
      if π₂ (ConcreteNamedSubstitution.result (π₁ children)) = 1 ∧
          π₂ (ConcreteNamedSubstitution.result (π₂ children)) = 1 then
        ConcreteNamedSubstitution.ok (Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
          (implicationInput (Arithmetic.pair (π₁ (ConcreteNamedSubstitution.result (π₁ children)))
            (π₁ (ConcreteNamedSubstitution.result (π₂ children)))))) else 0 := by
  by_cases hl : π₂ (ConcreteNamedSubstitution.result (π₁ children)) = 1 <;>
    by_cases hr : π₂ (ConcreteNamedSubstitution.result (π₂ children)) = 1 <;>
      simp [ConcreteNamedSubstitution.formulaRoot,ConcreteNamedSubstitution.result_payload,
        implicationInput,SyntaxPolynomial.formulaExpression,SyntaxPolynomial.power,
        ConcreteNamedSubstitution.allChildren,ConcreteNamedSubstitution.mapChildren,
        ConcreteNamedSubstitution.success,ConcreteNamedSubstitution.successfulValue,hl,hr]

/-- This complete branch equation retains the original child in the
equal-name case, even when its recursive option result is failure. -/
theorem formulaRoot_quantifier_result (V : Carrier) (π : ℕ → Carrier) (d : ℕ)
    (x replacement fv name body : M) :
    ConcreteNamedSubstitution.result (ConcreteNamedSubstitution.formulaRoot V π d
      (Arithmetic.pair x (Arithmetic.pair replacement fv)) (quantifierInput (Arithmetic.pair name body))) =
      if name = x then
        ConcreteNamedSubstitution.ok (Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
          (quantifierInput (Arithmetic.pair name (ConcreteNamedSubstitution.original body))))
      else if (ConcreteNamedSubstitution.member x (ConcreteNamedSubstitution.occurrences body) = 0 ∨
          ConcreteNamedSubstitution.member name fv = 0) ∧ π₂ (ConcreteNamedSubstitution.result body) = 1 then
        ConcreteNamedSubstitution.ok (Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
          (quantifierInput (Arithmetic.pair name (π₁ (ConcreteNamedSubstitution.result body))))) else 0 := by
  by_cases he : name = x <;>
    by_cases hc : ConcreteNamedSubstitution.member x (ConcreteNamedSubstitution.occurrences body) = 0 ∨
      ConcreteNamedSubstitution.member name fv = 0 <;>
    by_cases hs : π₂ (ConcreteNamedSubstitution.result body) = 1 <;>
      simp [ConcreteNamedSubstitution.formulaRoot,ConcreteNamedSubstitution.result_payload,
        quantifierInput,SyntaxPolynomial.formulaExpression,
        ConcreteNamedSubstitution.mapChildren,ConcreteNamedSubstitution.capture,
        ConcreteNamedSubstitution.success,ConcreteNamedSubstitution.successfulValue,he,hc,hs]

/-- An opaque scalar quantifier result, separated from concrete model
points so coordinate equalities can be applied by congruence. -/
def quantifierResultValue (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
    (x name old replacement child : M) : M :=
  if name = x then
    ConcreteNamedSubstitution.ok (Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
      (quantifierInput (Arithmetic.pair name old)))
  else if (ConcreteNamedSubstitution.member x (ConcreteNamedSubstitution.freeVariables V σ π d old) = 0 ∨
      ConcreteNamedSubstitution.member name (ConcreteNamedSubstitution.freeVariables V σ π d replacement) = 0) ∧
      π₂ child = 1 then
    ConcreteNamedSubstitution.ok (Coding.constructor true (SyntaxPolynomial.formulaExpression V π d)
      (quantifierInput (Arithmetic.pair name (π₁ child)))) else 0

theorem quantifierResultValue_payload (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
    (x replacement name body : M)
    (hmeta : ConcreteNamedSubstitution.occurrences body =
      ConcreteNamedSubstitution.freeVariables V σ π d (ConcreteNamedSubstitution.original body)) :
    quantifierResultValue V σ π d x name (ConcreteNamedSubstitution.original body) replacement
        (ConcreteNamedSubstitution.result body) =
      ConcreteNamedSubstitution.result (ConcreteNamedSubstitution.formulaRoot V π d
        (Arithmetic.pair x (Arithmetic.pair replacement
          (ConcreteNamedSubstitution.freeVariables V σ π d replacement)))
        (quantifierInput (Arithmetic.pair name body))) := by
  rw [formulaRoot_quantifier_result]
  simp only [quantifierResultValue,hmeta]

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
