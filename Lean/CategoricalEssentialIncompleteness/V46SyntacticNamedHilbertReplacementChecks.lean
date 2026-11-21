/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbertReplacement


/-! # Replacement of individual enumerated axioms in named proofs -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert.ReplacementChecks
open NamedFiniteSyntax NamedPostfixEncoding
variable (σ π : ℕ → SyntacticPredicates.Carrier) (d : ℕ)
variable (Γ Δ : SyntacticPredicates.Carrier)
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d
example
    (hAxiom : ∀ ψ : Fm, Γ.val.Evalb ![formulaCode ψ] → ψ.freeVariables = [] →
      SyntacticNamedHilbert.Derives σ π d Δ ψ)
    {φ : Fm} (h : SyntacticNamedHilbert.Derives σ π d Γ φ) :
    SyntacticNamedHilbert.Derives σ π d Δ φ := replace_axioms σ π d Γ Δ hAxiom h
end CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert.ReplacementChecks
