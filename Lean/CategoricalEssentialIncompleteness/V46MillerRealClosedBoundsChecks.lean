/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRealClosedBounds


/-! # Finite proof bounds for arbitrary extensions of T_a -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedBounds
open OrderedFieldSyntax RealClosedAxioms

example (a : Point) (Γ : Set ℕ) : Extends a Γ ↔
    ∀ φ : Formula,FiniteAxiomProof functionSymbols relationSymbols bound (theoryAxioms a) φ →
      FiniteAxiomProof functionSymbols relationSymbols bound Γ φ := extends_iff_proof_transport a Γ

example : asymmetryBody.FreeFor 0 one := asymmetry_freeFor_one
example : asymmetryBody.substitute 0 one=some asymmetryAtOne := asymmetry_substitute_one
example (n : ℕ) : asymmetryAtOneBody.FreeFor 1 (mul (natural 2) (c n)) := asymmetryAtOne_freeFor n
example (n : ℕ) : asymmetryAtOneBody.substitute 1 (mul (natural 2) (c n))=
    some (imp (lt one (mul (natural 2) (c n))) (negation (lt (mul (natural 2) (c n)) one))) :=
  asymmetryAtOne_substitute n

example (a : Point) (Γ : Set ℕ)
    (hΓ : ∀ φ : Formula,formulaCode φ∈RCFAxiomWords∪cutAxioms a →
      FiniteAxiomProof functionSymbols relationSymbols bound Γ φ)
    (n : ℕ) (h : (a n : ℝ)<1/2) :
    ∃ L : List ℕ,(∀ word∈L,word∈Γ) ∧
      SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (finiteCarrier L)
        (lt (mul (natural 2) (c n)) one) := lower_finite_support a Γ hΓ n h

example (a : Point) (Γ : Set ℕ)
    (hΓ : ∀ φ : Formula,formulaCode φ∈RCFAxiomWords∪cutAxioms a →
      FiniteAxiomProof functionSymbols relationSymbols bound Γ φ)
    (n : ℕ) (h : 1/2<(a n : ℝ)) :
    ∃ L : List ℕ,(∀ word∈L,word∈Γ) ∧
      SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (finiteCarrier L)
        (.neg (lt (mul (natural 2) (c n)) one)) := upper_finite_support a Γ hΓ n h

end CategoricalEssentialIncompleteness.V46.Miller.RealClosedBounds
