/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeInternalSyntax

/-!
# Canonical relative axiom graph

For a theory with a chosen Delta-one presentation, its Sigma and Pi
presentations agree in every PA model.  They therefore define a total
Boolean axiom graph with output-first coordinates `(bit,formulaCode)`.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeInternalAxiomGraph

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeInternalSyntax
open FailureOfComposition.NativeProofChecker

/-- The canonical graph uses the theory's actual chosen Delta-one
presentation, with acceptance bit one and rejection bit zero. -/
noncomputable def canonicalAxiomGraph (S : ArithmeticTheory) [S.Δ₁] :
    𝚺₁.Semisentence 2 := .mkSigma
  “b a. (b = 1 ∧ !S.Δ₁ch.sigma a) ∨ (b = 0 ∧ ¬!S.Δ₁ch.pi a)”

theorem canonicalAxiomGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (S : ArithmeticTheory) [S.Δ₁] (b a : V) :
    Semiformula.Evalb (M := V) ![b, a] (canonicalAxiomGraph S).val ↔
      (b = 1 ∧ a ∈ S.Δ₁Class) ∨ (b = 0 ∧ a ∉ S.Δ₁Class) := by
  simp [canonicalAxiomGraph]

theorem canonicalAxiomGraph_computational
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (S : ArithmeticTheory) [S.Δ₁] :
    ComputationalAxiomGraph (V := V) (canonicalAxiomGraph S) where
  existsUnique a := by
    simp only [canonicalAxiomGraph_iff]
    by_cases ha : a ∈ S.Δ₁Class <;> simp [ha]
  bit := by
    intro b a hb
    rcases (canonicalAxiomGraph_iff S b a).mp hb with (⟨rfl, _⟩ | ⟨rfl, _⟩) <;> simp

theorem canonicalAxiomGraph_theory
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (S : ArithmeticTheory) [S.Δ₁] :
    TheoryAxiomAgreement (V := V) (canonicalAxiomGraph S) S := by
  intro a _
  simp [canonicalAxiomGraph_iff]

/-- Only valid formula codes need numerical axiom agreement. -/
theorem canonicalAxiomGraph_numerical
    {ax : ℕ → Bool} {S : ArithmeticTheory} [S.Δ₁]
    (hax : AxiomAgreement ax S) : NumericalAxiomAgreement (canonicalAxiomGraph S) ax := by
  intro a ha
  rw [canonicalAxiomGraph_iff]
  cases h : ax a with
  | false =>
      have hn : a ∉ S.Δ₁Class := by
        intro hmem
        have := (hax a ha).mpr hmem
        simp [h] at this
      simp [hn]
  | true => simp [(hax a ha).mp h]

end FailureOfComposition.NativeInternalAxiomGraph
