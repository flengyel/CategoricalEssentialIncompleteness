/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDiagonalObstructionTuples

/-! # Proposition B.10 for the literal numerical tuple diagram -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ForkDiagonalObstruction.Checks

example (j : WalkingSpan) : (tupleDiagram.obj j).dimension =
    (match j with | .zero => 4 | .left => 2 | .right => 2) := by rcases j with _ | (_ | _) <;> rfl

example (k z a b : ℕ) : ((tupleDiagram.map WalkingSpan.Hom.fst).toFun
    ⟨(k,z,a,b), Set.mem_univ _⟩).val = (k,a) := rfl
example (k z a b : ℕ) : ((tupleDiagram.map WalkingSpan.Hom.snd).toFun
    ⟨(k,z,a,b), Set.mem_univ _⟩).val = (k,b) := rfl

example : ¬ Nonempty (DecidableVariables (⟨EffectiveFork.V⟩ : EffectiveFork.Total)) :=
  no_decidableVariables_total

example (d : tupleDiagram ⨯ tupleDiagram ⟶
    (⊤_ (WalkingSpan ⥤ NumericalTuples.Object)) ⨿ (⊤_ (WalkingSpan ⥤ NumericalTuples.Object))) :
    ¬ IsPullback (prod.lift (𝟙 tupleDiagram) (𝟙 tupleDiagram)) (terminal.from tupleDiagram) d coprod.inr :=
  no_diagonal_pullback d

end CategoricalEssentialIncompleteness.V46.ForkDiagonalObstruction.Checks
