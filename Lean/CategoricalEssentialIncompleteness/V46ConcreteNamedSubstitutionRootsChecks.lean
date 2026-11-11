/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionRoots

/-! Explicit PA-model and standard primitive-recursion statement checks. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
open CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example (V : Carrier) (π : ℕ → Carrier) (d : ℕ) (x t fvt old fvbody : M) :
    result (formulaRoot V π d ⟪x,⟪t,fvt⟫⟫ ⟪⟪x,payload old fvbody 0 0⟫,1⟫) =
      ok (constructor true (SyntaxPolynomial.formulaExpression V π d) ⟪⟪x,old⟫,1⟫) := by
  simpa using formulaRoot_equal_binder_result V π d x t fvt (payload old fvbody 0 0)
example (V : Carrier) (σ : ℕ → Carrier) (d : ℕ) :
    Primrec₂ (termRoot V σ d : ℕ → ℕ → ℕ) := termRoot_primrec V σ d
example (V : Carrier) (π : ℕ → Carrier) (d : ℕ) :
    Primrec₂ (formulaRoot V π d : ℕ → ℕ → ℕ) := formulaRoot_primrec V π d
