/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedHilbertPropositional

/-! # Raw named-calculus statement checks -/

@[expose] public section

namespace CategoricalEssentialIncompleteness.V46.NamedHilbertPropositionalChecks
open SyntacticPredicates NamedHilbertPropositional
variable (σ π : ℕ → Carrier) (d : ℕ) (Γ : Carrier)

example (φ : NamedFiniteSyntax.Formula (NamedPostfixEncoding.Symbols σ)
    (NamedPostfixEncoding.Symbols π) d) :
    SyntacticNamedHilbert.Derives σ π d Γ (.imp (.neg (.neg φ)) φ) :=
  doubleNegElim σ π d Γ φ

example (φ ψ : NamedFiniteSyntax.Formula (NamedPostfixEncoding.Symbols σ)
    (NamedPostfixEncoding.Symbols π) d) :
    SyntacticNamedHilbert.Derives σ π d Γ
      (.imp φ (.imp ψ (.neg (.imp φ (.neg ψ))))) :=
  conjunction_intro σ π d Γ φ ψ

example (φ ψ : NamedFiniteSyntax.Formula (NamedPostfixEncoding.Symbols σ)
    (NamedPostfixEncoding.Symbols π) d) :
    SyntacticNamedHilbert.Derives σ π d Γ
      (.imp (.imp (.neg ψ) (.neg φ)) (.imp φ ψ)) := by
  classical
  let S : System σ π d := ⟨Γ⟩
  apply (system_provable_iff σ π d S _).mp
  exact FFL.Entailment.elim_contra

end CategoricalEssentialIncompleteness.V46.NamedHilbertPropositionalChecks
