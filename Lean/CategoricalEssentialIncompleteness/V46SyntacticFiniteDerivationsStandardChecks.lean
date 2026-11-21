/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticFiniteDerivationsStandard


/-! # Standard constructed proof codes have explicit finite derivations -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticFiniteDerivations
namespace CategoricalEssentialIncompleteness.V46.SyntacticFiniteDerivations.StandardChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T]
example {Fm : PredicateCategory T} {N : ℕ} (R : RulePresentation Fm N)
    (φ : SyntacticLists.Obj T ℕ Fm) :
    Derives T ℕ R φ ↔
      ∃ p : SyntacticLists.Obj T ℕ (SyntacticDerivation.derivationAlgebra T R).a.left,
        (SyntacticLists.F T ℕ).map (SyntacticDerivation.derivationAlgebra T R).a.hom p = φ :=
  standard_iff T R φ
end CategoricalEssentialIncompleteness.V46.SyntacticFiniteDerivations.StandardChecks
