/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedFiniteSemantics

/-! # The seven named-variable schemes and their two inference rules

These semantic lemmas are on external finite trees. Their application to
the arithmetic derivation object requires the proved standard-code comparison.
-/

@[expose] public section

universe u v w
namespace CategoricalEssentialIncompleteness.V46.NamedFiniteSyntax.Formula
variable {Sig : ℕ → Type u} {Rel : ℕ → Type v} {d : ℕ} {K : Type w}
  (functions : ∀ n : Fin (d + 1), Sig n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Rel n.val → (Fin n.val → K) → Prop)

def Valid (φ : Formula Sig Rel d) : Prop := ∀ ρ : ℕ → K, φ.Holds functions relations ρ

theorem valid_one (φ ψ : Formula Sig Rel d) :
    Valid functions relations (.imp φ (.imp ψ φ)) := by
  intro ρ hφ _
  exact hφ

theorem valid_two (φ ψ χ : Formula Sig Rel d) :
    Valid functions relations
      (.imp (.imp φ (.imp ψ χ)) (.imp (.imp φ ψ) (.imp φ χ))) := by
  intro ρ h₁ h₂ hφ
  exact h₁ hφ (h₂ hφ)

theorem valid_three (φ ψ : Formula Sig Rel d) :
    Valid functions relations (.imp (.imp (.neg ψ) (.neg φ)) (.imp φ ψ)) := by
  intro ρ h hφ
  classical
  by_contra hψ
  exact h hψ hφ

theorem valid_instantiation (φ ψ : Formula Sig Rel d) (x : ℕ) (t : Term Sig d)
    (h : φ.substitute x t = some ψ) :
    Valid functions relations (.imp (.all x φ) ψ) := by
  intro ρ hall
  apply (holds_substitute functions relations φ ψ t x ρ h).mpr
  exact hall (t.evaluate functions ρ)

theorem valid_distribution (φ ψ : Formula Sig Rel d) (x : ℕ)
    (hx : x ∉ φ.freeVariables) :
    Valid functions relations (.imp (.all x (.imp φ ψ)) (.imp φ (.all x ψ))) := by
  intro ρ hall hφ a
  exact hall a ((holds_update_absent functions relations φ x ρ a hx).mpr hφ)

theorem valid_reflexivity (t : Term Sig d) :
    Valid functions relations (.equal t t) := by
  intro ρ
  rfl

theorem valid_equality (φ φu φt : Formula Sig Rel d) (u t : Term Sig d) (x : ℕ)
    (hu : φ.substitute x u = some φu) (ht : φ.substitute x t = some φt) :
    Valid functions relations (.imp (.equal u t) (.imp φu φt)) := by
  intro ρ he hφ
  have hφu := (holds_substitute functions relations φ φu u x ρ hu).mp hφ
  apply (holds_substitute functions relations φ φt t x ρ ht).mpr
  change u.evaluate functions ρ = t.evaluate functions ρ at he
  simpa only [he] using hφu

theorem valid_modusPonens (φ ψ : Formula Sig Rel d)
    (himp : Valid functions relations (.imp φ ψ)) (hφ : Valid functions relations φ) :
    Valid functions relations ψ := by
  intro ρ
  exact himp ρ (hφ ρ)

theorem valid_generalization (φ : Formula Sig Rel d) (x : ℕ)
    (hφ : Valid functions relations φ) : Valid functions relations (.all x φ) := by
  intro ρ a
  exact hφ (Function.update ρ x a)

theorem valid_negation_disjoint [Nonempty K] (φ : Formula Sig Rel d)
    (hφ : Valid functions relations φ) (hnot : Valid functions relations (.neg φ)) : False := by
  classical
  let ρ : ℕ → K := fun _ => Classical.choice (inferInstance : Nonempty K)
  exact hnot ρ (hφ ρ)

end CategoricalEssentialIncompleteness.V46.NamedFiniteSyntax.Formula
