/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPostfixComparison
public import CategoricalEssentialIncompleteness.V46NamedFiniteSyntax

/-! # Literal named finite Hilbert derivations for a Sigma-one enumeration

The proof constructors use the seven manuscript schemes, generalization
and ordered modus ponens. Substitution is the existing named partial
operation; its free-for condition remains independently defined.
-/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert
open NamedFiniteSyntax NamedPostfixEncoding
variable (σ π : ℕ → SyntacticPredicates.Carrier) (d : ℕ)
variable (Γ : SyntacticPredicates.Carrier)
local notation "Tm" => NamedFiniteSyntax.Term (NamedPostfixEncoding.Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula
  (NamedPostfixEncoding.Symbols σ) (NamedPostfixEncoding.Symbols π) d

/-- A finite proof retains the original variable names and all ordered
premises. Γ axioms are filtered by literal sentencehood. -/
inductive Derives : Fm → Prop
  | «axiom» (φ : Fm) (enumerated : Γ.val.Evalb ![formulaCode φ])
      (sentence : φ.freeVariables = []) : Derives φ
  | one (φ ψ : Fm) : Derives (.imp φ (.imp ψ φ))
  | two (φ ψ χ : Fm) :
      Derives (.imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ)))
  | three (φ ψ : Fm) : Derives (.imp (.imp (.neg ψ) (.neg φ)) (.imp φ ψ))
  | instantiation (x : ℕ) (φ : Fm) (t : Tm) (ψ : Fm)
      (freeFor : φ.FreeFor x t) (substitution : φ.substitute x t = some ψ) :
      Derives (.imp (.all x φ) ψ)
  | distribution (x : ℕ) (φ ψ : Fm) (absent : x ∉ φ.freeVariables) :
      Derives (.imp (.all x (.imp φ ψ)) (.imp φ (.all x ψ)))
  | reflexivity (t : Tm) : Derives (.equal t t)
  | equality (x : ℕ) (φ : Fm) (u t : Tm) (ψ χ : Fm)
      (freeForLeft : φ.FreeFor x u) (freeForRight : φ.FreeFor x t)
      (substitutionLeft : φ.substitute x u = some ψ)
      (substitutionRight : φ.substitute x t = some χ) :
      Derives (.imp (.equal u t) (.imp ψ χ))
  | generalization (x : ℕ) {φ : Fm} (proof : Derives φ) : Derives (.all x φ)
  | modusPonens {φ ψ : Fm} (antecedent : Derives φ)
      (implication : Derives (.imp φ ψ)) : Derives ψ

/-- Every independent free-for instance has its uniquely computed
successful output, so the scheme constructor excludes no intended case. -/
theorem instantiation_exists (x : ℕ) (φ : Fm) (t : Tm) (h : φ.FreeFor x t) :
    ∃ ψ : Fm, φ.substitute x t = some ψ ∧ Derives σ π d Γ (.imp (.all x φ) ψ) := by
  have hs := (NamedFiniteSyntax.Formula.substitute_isSome_iff φ x t).mpr h
  cases he : φ.substitute x t with
  | none => simp_all
  | some ψ => exact ⟨ψ,rfl,.instantiation x φ t ψ h he⟩

/-- Both successful outputs are derived from the two independent
free-for conditions, preserving the original shared body and name. -/
theorem equality_exists (x : ℕ) (φ : Fm) (u t : Tm)
    (hu : φ.FreeFor x u) (ht : φ.FreeFor x t) :
    ∃ ψ χ : Fm, φ.substitute x u = some ψ ∧ φ.substitute x t = some χ ∧
      Derives σ π d Γ (.imp (.equal u t) (.imp ψ χ)) := by
  obtain ⟨ψ,hψ,_⟩ := instantiation_exists σ π d Γ x φ u hu
  obtain ⟨χ,hχ,_⟩ := instantiation_exists σ π d Γ x φ t ht
  exact ⟨ψ,χ,hψ,hχ,.equality x φ u t ψ χ hu ht hψ hχ⟩

end CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert
