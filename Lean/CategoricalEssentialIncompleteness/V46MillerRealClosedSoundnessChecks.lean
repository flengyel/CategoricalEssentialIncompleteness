/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerRealClosedSoundness


/-! # Statement checks in `V46MillerRealClosedSoundnessChecks` -/

@[expose] public section
namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedSoundness
open OrderedFieldSyntax RealClosedAxioms

example (a : Point) (L : List ℕ) (hL : ∀ word∈L,word∈RCFAxiomWords∪cutAxioms a)
    (φ : Formula)
    (h : SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (finiteCarrier L) φ) :
    ∀ ρ : ℕ → ℝ,φ.Holds (Semantics.functions (fun i => (a i : ℝ)))
      (Semantics.relations (K := ℝ)) ρ := native_finite_real_sound a L hL h

example (a : Point) (φ : Formula)
    (h : ∃ L : List ℕ,(∀ word∈L,word∈RCFAxiomWords∪cutAxioms a) ∧
      SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (finiteCarrier L) φ) :
    ∀ ρ : ℕ → ℝ,φ.Holds (Semantics.functions (fun i => (a i : ℝ)))
      (Semantics.relations (K := ℝ)) ρ := finiteProof_real_sound a h

example (a : Point) : ∀ φ : Formula,¬(
    (∃ L : List ℕ,(∀ word∈L,word∈RCFAxiomWords∪cutAxioms a) ∧
      SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (finiteCarrier L) φ) ∧
    (∃ L : List ℕ,(∀ word∈L,word∈RCFAxiomWords∪cutAxioms a) ∧
      SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (finiteCarrier L) (.neg φ))) :=
  native_consistency a

end CategoricalEssentialIncompleteness.V46.Miller.RealClosedSoundness
