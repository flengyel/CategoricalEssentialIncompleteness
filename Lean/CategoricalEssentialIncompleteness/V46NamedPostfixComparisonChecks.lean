/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPostfixComparison


/-! # Statement checks in `V46NamedPostfixComparisonChecks` -/

@[expose] public section
noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NamedPostfixComparisonChecks
open NamedPostfixEncoding
variable (σ π : ℕ → Carrier) (d : ℕ)
example : Function.Injective (termCode (σ := σ) (d := d)) := termCode_injective
example : Function.Injective (formulaCode (σ := σ) (π := π) (d := d)) := formulaCode_injective
example : NamedFiniteSyntax.Term (Symbols σ) d ≃ termWords σ π d := termEquiv σ π d
example : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d ≃ formulaWords σ π d :=
  formulaEquiv σ π d
example (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    (formulaEquiv σ π d φ).val = formulaCode φ := formulaEquiv_val φ
end CategoricalEssentialIncompleteness.V46.NamedPostfixComparisonChecks
