/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbert


/-! # Named finite Hilbert derivations for a Sigma-one enumeration -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert.Checks
open NamedFiniteSyntax NamedPostfixEncoding
variable (σ π : ℕ → SyntacticPredicates.Carrier) (d : ℕ) (Γ : SyntacticPredicates.Carrier)
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

example (x : ℕ) (φ : Fm) (t : Tm) (h : φ.FreeFor x t) :
    ∃ ψ : Fm, φ.substitute x t = some ψ ∧ Derives σ π d Γ (.imp (.all x φ) ψ) :=
  instantiation_exists σ π d Γ x φ t h

example (φ ψ : Fm) (p : Derives σ π d Γ φ) (q : Derives σ π d Γ (.imp φ ψ)) :
    Derives σ π d Γ ψ := .modusPonens p q

example (x : ℕ) (φ : Fm) (t : Tm) (r : Fm)
    (hff : φ.FreeFor x t) (hs : φ.substitute x t = some r) :
    Derives σ π d Γ (.imp (.all x φ) r) := .instantiation x φ t r hff hs
end CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert.Checks
