/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRealClosedAxiomsSemantics
public import CategoricalEssentialIncompleteness.V46MillerFiniteAxiomProofs
public import CategoricalEssentialIncompleteness.V46NamedFiniteSoundness

/-! # The constructed real model is sound for finite T_a proofs

Each nonlogical leaf has its original finiteCarrier support and sentence guard. Its
truth follows from the T_a word set in the constructed real interpretation. The seven
schemes and both inference rules are the already proved named-variable rules, with
their original substitutions.
-/

@[expose] public section
noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedSoundness
open OrderedFieldSyntax RealClosedAxioms

theorem native_finite_real_sound (a : Point) (L : List ℕ)
    (hL : ∀ word∈L,word∈theoryAxioms a) {φ : Formula}
    (h : SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (finiteCarrier L) φ) :
    ∀ ρ : ℕ → ℝ,φ.Holds (Semantics.functions (fun i => (a i : ℝ)))
      (Semantics.relations (K := ℝ)) ρ := by
  let F := Semantics.functions (fun i => (a i : ℝ))
  let R := Semantics.relations (K := ℝ)
  change NamedFiniteSyntax.Formula.Valid F R φ
  induction h with
  | «axiom» ψ hψ _ =>
      exact Semantics.theory_formula_valid a ψ (hL _ ((finiteCarrier_eval L _).mp hψ))
  | one ψ χ => exact NamedFiniteSyntax.Formula.valid_one F R ψ χ
  | two ψ χ ξ => exact NamedFiniteSyntax.Formula.valid_two F R ψ χ ξ
  | three ψ χ => exact NamedFiniteSyntax.Formula.valid_three F R ψ χ
  | instantiation x ψ t χ _ hsub =>
      exact NamedFiniteSyntax.Formula.valid_instantiation F R ψ χ x t hsub
  | distribution x ψ χ habsent =>
      exact NamedFiniteSyntax.Formula.valid_distribution F R ψ χ x habsent
  | reflexivity t => exact NamedFiniteSyntax.Formula.valid_reflexivity F R t
  | equality x ψ u t χ ξ _ _ hsubu hsubt =>
      exact NamedFiniteSyntax.Formula.valid_equality F R ψ χ ξ u t x hsubu hsubt
  | generalization x _ ih =>
      exact NamedFiniteSyntax.Formula.valid_generalization F R _ x ih
  | modusPonens _ _ ihψ ihimp =>
      exact NamedFiniteSyntax.Formula.valid_modusPonens F R _ _ ihimp ihψ

/-- The model premise is discharged by the constructed real model of T_a. -/
theorem finiteProof_real_sound (a : Point) {φ : Formula}
    (h : FiniteAxiomProof functionSymbols relationSymbols bound (theoryAxioms a) φ) :
    ∀ ρ : ℕ → ℝ,φ.Holds (Semantics.functions (fun i => (a i : ℝ)))
      (Semantics.relations (K := ℝ)) ρ := by
  obtain ⟨L,hL,hφ⟩ := h
  exact native_finite_real_sound a L hL hφ

/-- Both proof supports are finite supports in T_a; no common enumeration or
proof-selection assumption is introduced. -/
theorem no_finiteProof_pair (a : Point) (φ : Formula) :
    ¬(FiniteAxiomProof functionSymbols relationSymbols bound (theoryAxioms a) φ ∧
      FiniteAxiomProof functionSymbols relationSymbols bound (theoryAxioms a) (.neg φ)) := by
  rintro ⟨hφ,hneg⟩
  have hp := finiteProof_real_sound a hφ (fun _ => 0)
  have hn := finiteProof_real_sound a hneg (fun _ => 0)
  exact hn hp

theorem native_consistency (a : Point) : ∀ φ : Formula,
    ¬(FiniteAxiomProof functionSymbols relationSymbols bound (theoryAxioms a) φ ∧
      FiniteAxiomProof functionSymbols relationSymbols bound (theoryAxioms a) (.neg φ)) := no_finiteProof_pair a

end CategoricalEssentialIncompleteness.V46.Miller.RealClosedSoundness
