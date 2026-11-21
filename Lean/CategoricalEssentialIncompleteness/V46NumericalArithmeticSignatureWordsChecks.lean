/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticSignatureWords


/-! # The computable identity-on-word signature chart -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SignatureRelabel.Checks
open SyntacticSyntax NamedPostfixEncoding
variable {σ τ π ρ : ℕ → Carrier} {d : ℕ}
variable (h : ∀ (k n : ℕ), (σ k).val.Evalb ![n] ↔ (τ k).val.Evalb ![n])
  (j : ∀ (k n : ℕ), (π k).val.Evalb ![n] ↔ (ρ k).val.Evalb ![n])
example (b : Bool) : wordObject b σ π d ≅ wordObject b τ ρ d :=
  wordIso (σ := σ) (τ := τ) (π := π) (ρ := ρ) (d := d) h j b
example (b : Bool) :
    let e : wordObject b σ π d ≅ wordObject b τ ρ d :=
      wordIso (σ := σ) (τ := τ) (π := π) (ρ := ρ) (d := d) h j b
    ∀ x : PredicateInterpretation.Obj ℕ
      (Postfix.plainCarrier b (termPolynomial σ d) (formulaPolynomial π d)),
      ((e.hom.toFun x).val : ℕ) = (x.val : ℕ) := by
  dsimp only
  intro x
  exact wordIso_hom_value (σ := σ) (τ := τ) (π := π) (ρ := ρ) (d := d) h j b x
example (b : Bool) :
    let e : wordObject b σ π d ≅ wordObject b τ ρ d :=
      wordIso (σ := σ) (τ := τ) (π := π) (ρ := ρ) (d := d) h j b
    ∀ x : PredicateInterpretation.Obj ℕ
      (Postfix.plainCarrier b (termPolynomial τ d) (formulaPolynomial ρ d)),
      ((e.inv.toFun x).val : ℕ) = (x.val : ℕ) := by
  dsimp only
  intro x
  exact wordIso_inv_value (σ := σ) (τ := τ) (π := π) (ρ := ρ) (d := d) h j b x
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SignatureRelabel.Checks
