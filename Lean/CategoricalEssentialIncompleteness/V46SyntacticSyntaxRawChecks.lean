/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRaw

/-! # Checks for genuine Sigma-one syntax operation inputs -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates SyntacticSyntax

example (V : Carrier) (σ : ℕ → Carrier) (d : ℕ) : RawPolynomial :=
  SyntaxPolynomial.termExpression V σ d

example (V : Carrier) (π : ℕ → Carrier) (d : ℕ) : RawPolynomial :=
  SyntaxPolynomial.formulaExpression V π d

variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)

example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (p u : M)
    (h : (rawFiber P X Y A.termProjection.graph A.formulaProjection.graph a).val.Evalb
      ![p, u]) : ∃! x : M, A.termOp.val.Evalb ![p, u, x] := A.term_total_model p u h

example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (p u y y' : M)
    (h : A.formulaOp.val.Evalb ![p, u, y]) (h' : A.formulaOp.val.Evalb ![p, u, y']) :
    y = y' := A.formula_functional_model p u y y' h h'
