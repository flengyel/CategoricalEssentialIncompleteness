/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbert

/-! # Replacement of individual enumerated axioms in named proofs

The replacement premise concerns the sentence axioms only. The proof transforms the
finite derivation and retains every original name, ordered premise, free-for proof and
successful substitution equation.
-/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert
open NamedFiniteSyntax NamedPostfixEncoding
variable (σ π : ℕ → SyntacticPredicates.Carrier) (d : ℕ)
variable (Γ Δ : SyntacticPredicates.Carrier)
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

/-- Replacing each enumerated sentence axiom by a finite Δ-proof transforms every Γ-proof
into a literal Δ-proof. -/
theorem replace_axioms
    (hAxiom : ∀ ψ : Fm, Γ.val.Evalb ![formulaCode ψ] → ψ.freeVariables = [] →
      Derives σ π d Δ ψ)
    {φ : Fm} (h : Derives σ π d Γ φ) : Derives σ π d Δ φ := by
  induction h with
  | «axiom» ψ enumerated sentence => exact hAxiom ψ enumerated sentence
  | one φ ψ => exact .one φ ψ
  | two φ ψ χ => exact .two φ ψ χ
  | three φ ψ => exact .three φ ψ
  | instantiation x φ t ψ freeFor substitution =>
      exact .instantiation x φ t ψ freeFor substitution
  | distribution x φ ψ absent => exact .distribution x φ ψ absent
  | reflexivity t => exact .reflexivity t
  | equality x φ u t ψ χ freeForLeft freeForRight substitutionLeft substitutionRight =>
      exact .equality x φ u t ψ χ freeForLeft freeForRight substitutionLeft substitutionRight
  | @generalization x φ proof ih => exact .generalization x ih
  | @modusPonens φ ψ antecedent implication ihAntecedent ihImplication =>
      exact .modusPonens ihAntecedent ihImplication

end CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert
