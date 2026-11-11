/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionAlgorithmTyped

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
example (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) (x t body : M)
    (ht : (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![t])
    (hb : (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![body]) :
    substitutionFreeFor V σ π d x t body = 1 ↔
      π₂ (substitutionResult V σ π d x t body) = 1 :=
  substitutionFreeFor_iff_success V σ π d x t body ht hb

example (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) (formula : Bool) (x t word : M)
    (ht : (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![t])
    (hw : (Postfix.carrier formula (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![word]) :
    (if formula then formulaPayloadCarrier V σ π d else termPayloadCarrier V σ π d).val.Evalb
      ![substitutionPayload V σ π d x t word] :=
  substitutionPayload_carrier V σ π d formula x t word ht hw
example (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) (x t body : M)
    (hx : V.val.Evalb ![x])
    (hb : (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![body]) :
    substitutionFreeFor V σ π d x t
      (constructor true (SyntaxPolynomial.formulaExpression V π d) ⟪⟪x,body⟫,1⟫) = 1 :=
  substitutionFreeFor_equal_binder V σ π d x t body hx hb
