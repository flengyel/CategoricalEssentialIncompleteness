/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedFiniteSemantics


/-! # Statement checks in `V46NamedFiniteSemanticsChecks` -/

@[expose] public section
universe u v w
namespace CategoricalEssentialIncompleteness.V46.NamedFiniteSemanticsChecks
open NamedFiniteSyntax
variable {Sig : ℕ → Type u} {Rel : ℕ → Type v} {d : ℕ} {K : Type w}
example (functions : ∀ n : Fin (d + 1), Sig n.val → (Fin n.val → K) → K)
    (relations : ∀ n : Fin (d + 1), Rel n.val → (Fin n.val → K) → Prop)
    (φ ψ : Formula Sig Rel d) (t : Term Sig d) (x : ℕ) (ρ : ℕ → K)
    (h : φ.substitute x t = some ψ) :
    ψ.Holds functions relations ρ ↔
      φ.Holds functions relations (Function.update ρ x (t.evaluate functions ρ)) :=
  Formula.holds_substitute functions relations φ ψ t x ρ h
example (functions : ∀ n : Fin (d + 1), Sig n.val → (Fin n.val → K) → K)
    (relations : ∀ n : Fin (d + 1), Rel n.val → (Fin n.val → K) → Prop)
    (φ : Formula Sig Rel d) (ρ τ : ℕ → K)
    (h : ∀ x, x ∈ φ.freeVariables → ρ x = τ x) :
    φ.Holds functions relations ρ ↔ φ.Holds functions relations τ :=
  Formula.holds_congr functions relations φ h
end CategoricalEssentialIncompleteness.V46.NamedFiniteSemanticsChecks
