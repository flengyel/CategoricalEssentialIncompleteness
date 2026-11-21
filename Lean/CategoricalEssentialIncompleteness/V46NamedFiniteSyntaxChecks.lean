/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedFiniteSyntax


/-! # Finite syntax with named binders -/

@[expose] public section
universe u v w
namespace CategoricalEssentialIncompleteness.V46.NamedFiniteSyntaxChecks
open NamedFiniteSyntax
variable {Sig : ℕ → Type u} {Rel : ℕ → Type v} {d : ℕ} {K : Type w}
example (functions : ∀ n : Fin (d + 1), Sig n.val → (Fin n.val → K) → K)
    (r t : Term Sig d) (x : ℕ) (ρ : ℕ → K) :
    (r.substitute x t).evaluate functions ρ =
      r.evaluate functions (Function.update ρ x (t.evaluate functions ρ)) :=
  Term.evaluate_substitute functions r t x ρ
example (φ : Formula Sig Rel d) (t : Term Sig d) (x : ℕ) :
    (Formula.all x φ).substitute x t = some (Formula.all x φ) := by
  simp [Formula.substitute]
example (φ : Formula Sig Rel d) (t : Term Sig d) (x : ℕ) :
    (φ.substitute x t).isSome = true ↔ φ.FreeFor x t :=
  Formula.substitute_isSome_iff φ x t
end CategoricalEssentialIncompleteness.V46.NamedFiniteSyntaxChecks
