/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticFiniteDerivations

/-! # Standard constructed proof codes have explicit finite derivations -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticFiniteDerivations
open SyntacticDerivation SyntacticDerivation.StandardInduction
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T]
variable {Fm : PredicateCategory T} {bound : ℕ} (R : RulePresentation Fm bound)

/-- This direction is deliberately standard-model only. Arithmetic
node-count induction exposes the finite tree; no Set-initiality premise
is assumed and no such statement is made about nonstandard proof codes. -/
theorem standard_complete (p : Obj T ℕ (derivationAlgebra T R).a.left) :
    Derives T ℕ R ((F T ℕ).map (derivationAlgebra T R).a.hom p) := by
  apply conclusion_induction T R (fun φ => Derives T ℕ R φ) ?_ p
  intro i input ih
  let label := (F T ℕ).map
    (pullback.fst (R.premises i) (finitePowerMap (derivationAlgebra T R).a.hom i.val)) input
  have children : ∀ k : Fin i.val,
      Derives T ℕ R ((F T ℕ).map (R.premises i ≫ finiteChild T Fm i.val k) label) := by
    intro k
    dsimp only [label]
    have h := ih k
    erw [typedPremise,Functor.map_comp_apply,Functor.map_comp_apply] at h
    erw [Functor.map_comp_apply]
    exact h
  have h : Derives T ℕ R ((F T ℕ).map (R.conclusion i) label) :=
    .node i label children
  dsimp only [label] at h
  change Derives T ℕ R ((F T ℕ).map
    (pullback.fst (R.premises i) (finitePowerMap (derivationAlgebra T R).a.hom i.val) ≫
      R.conclusion i) input)
  erw [Functor.map_comp_apply]
  exact h

/-- Finite typed rule trees coincide with the conclusions of the
actual constructed standard proof carrier. -/
theorem standard_iff (φ : Obj T ℕ Fm) :
    Derives T ℕ R φ ↔ ∃ p : Obj T ℕ (derivationAlgebra T R).a.left,
      (F T ℕ).map (derivationAlgebra T R).a.hom p = φ := by
  constructor
  · exact realizes T ℕ R
  · rintro ⟨p,hp⟩
    exact hp ▸ standard_complete T R p

end CategoricalEssentialIncompleteness.V46.SyntacticFiniteDerivations
