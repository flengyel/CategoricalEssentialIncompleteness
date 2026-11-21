/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedHilbertQuantifiers


/-! # Derived first-order rules in the named calculus -/

@[expose] public section
open FFL
namespace CategoricalEssentialIncompleteness.V46.NamedHilbertQuantifiersChecks
open SyntacticPredicates NamedPostfixEncoding NamedFiniteSyntax

variable (σ π : ℕ → Carrier) (d : ℕ) (Γ : Carrier)
local notation "Tm" => Term (Symbols σ) d
local notation "Fm" => Formula (Symbols σ) (Symbols π) d

example (φ : Fm) (x : ℕ) : φ.FreeFor x (.var x) :=
  NamedHilbertQuantifiers.formula_freeFor_self φ x

example (φ : Fm) (x : ℕ) : φ.substitute x (.var x) = some φ :=
  NamedHilbertQuantifiers.formula_substitute_self φ x

example (φ : Fm) (x : ℕ) (t : Tm) (hx : x ∉ φ.freeVariables) :
    φ.substitute x t = some φ :=
  NamedHilbertQuantifiers.formula_substitute_absent φ x t hx

example (x : ℕ) (φ ψ : Fm)
    (h : SyntacticNamedHilbert.Derives σ π d Γ (.imp φ ψ)) :
    SyntacticNamedHilbert.Derives σ π d Γ (.imp (.all x φ) (.all x ψ)) :=
  NamedHilbertQuantifiers.all_mono σ π d Γ x h

example (x y : ℕ) (φ ψ : Fm)
    (hff : φ.FreeFor x (.var y))
    (hs : φ.substitute x (.var y) = some ψ)
    (hy : y ∉ (Formula.all x φ).freeVariables) :
    SyntacticNamedHilbert.Derives σ π d Γ (.imp (.all x φ) (.all y ψ)) :=
  NamedHilbertQuantifiers.all_rename_forward σ π d Γ x y φ ψ hff hs hy

example (x : ℕ) (φ ψ : Fm) (t : Tm)
    (hff : φ.FreeFor x t) (hs : φ.substitute x t = some ψ) :
    SyntacticNamedHilbert.Derives σ π d Γ (.imp ψ (.neg (.all x (.neg φ)))) :=
  NamedHilbertQuantifiers.exists_intro σ π d Γ x φ ψ t hff hs

end CategoricalEssentialIncompleteness.V46.NamedHilbertQuantifiersChecks
