/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticLiteralSignature


/-! # Statement checks in `V46NumericalArithmeticLiteralSignatureChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.LiteralSignature.Checks
open NamedFiniteSyntax NamedPostfixEncoding
example {σ π : ℕ → Carrier} {d : ℕ} (φ : Formula (Symbols σ) (Symbols π) d) :
    formulaCode (formulaEquiv φ) = formulaCode φ := formula_code φ
example (Γ : Carrier) (hΓ : ∀ word : ℕ,
    ArithmeticIndexedPAEnumeration.axiomCodes.val.Evalb ![word] → Γ.val.Evalb ![word])
    (φ : NamedArithmeticSignature.Formula) (hφ : ArithmeticNamedAxiomComparison.PAAxiom φ) :
    SyntacticNamedHilbert.Derives (coefficients NamedArithmeticSignature.functionSymbols)
      (coefficients NamedArithmeticSignature.relationSymbols) NamedArithmeticSignature.bound Γ
      (formulaEquiv φ) := arithmetic_PA Γ hΓ φ hφ
example {σ π : ℕ → Carrier} {d : ℕ} (Γ : Carrier) (φ : Formula (Symbols σ) (Symbols π) d) :
    SyntacticNamedHilbert.Derives (coefficients σ) (coefficients π) d Γ (formulaEquiv φ) ↔
      SyntacticNamedHilbert.Derives σ π d Γ φ := derives_iff Γ φ
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.LiteralSignature.Checks
