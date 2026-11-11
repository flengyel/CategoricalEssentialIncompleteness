/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPostfixPlainComparison


/-! # Statement checks in `V46NamedPostfixPlainComparisonChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NamedPostfixPlainComparisonChecks
open NamedPostfixEncoding NamedPostfixPlainComparison SyntacticSyntax
variable (σ π : ℕ → Carrier) (d : ℕ)
example : NamedFiniteSyntax.Term (Symbols σ) d ≃
    (PredicateInterpretation.functor 𝗣𝗔 ℕ).obj
      (plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d).algebra.a.1 := plainTermModelEquiv σ π d
example : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d ≃
    (PredicateInterpretation.functor 𝗣𝗔 ℕ).obj
      (plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d).algebra.a.2 := plainFormulaModelEquiv σ π d
example (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    (plainFormulaModelEquiv σ π d φ).val = formulaCode φ := plainFormulaModelEquiv_val φ
end CategoricalEssentialIncompleteness.V46.NamedPostfixPlainComparisonChecks
