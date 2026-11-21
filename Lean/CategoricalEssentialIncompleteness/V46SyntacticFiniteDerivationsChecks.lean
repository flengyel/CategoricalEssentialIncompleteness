/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticFiniteDerivations


/-! # Explicit finite typed derivations and the constructed proof object -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticFiniteDerivations
namespace CategoricalEssentialIncompleteness.V46.SyntacticFiniteDerivations.CoreChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
example {Fm : PredicateCategory T} {N : ℕ} (R : RulePresentation Fm N)
    (φ : SyntacticLists.Obj T M Fm) (h : Derives T M R φ) :
    ∃ p : SyntacticLists.Obj T M (SyntacticDerivation.derivationAlgebra T R).a.left,
      (SyntacticLists.F T M).map (SyntacticDerivation.derivationAlgebra T R).a.hom p = φ :=
  realizes T M R h
end CategoricalEssentialIncompleteness.V46.SyntacticFiniteDerivations.CoreChecks
