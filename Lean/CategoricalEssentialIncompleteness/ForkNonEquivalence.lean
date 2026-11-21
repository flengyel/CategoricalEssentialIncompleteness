/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.TerminalForkSupports
public import CategoricalEssentialIncompleteness.ClassicalSplitEquivalence
public import CategoricalEssentialIncompleteness.EffectiveForkSplitEquivalence

/-! # The nonnumerical recursion category is not restriction equivalent to classical Rec -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness

/-- Proposition B.10's categorical distinction. The equivalence is required only to
preserve restrictions in its two directions; ranges, products and coproducts need not
be included as additional hypotheses. -/
theorem fork_not_restriction_equivalent
    (e : EffectiveFork.Recursion.Rec ≌ ClassicalPrograms.Rec)
    (hF : PreservesRestriction e.functor) (hG : PreservesRestriction e.inverse) : False := by
  let R := EffectiveFork.Recursion.realization
  have hR : PreservesRestriction R := fun f => EffectiveFork.Recursion.realization_rst f
  let eR := hR.totalEquivalence
  let X := eR.inverse.obj ⟨EffectiveFork.terminalFork⟩
  have hX : IsTerminal X := EffectiveFork.terminalFork_isTerminal.isTerminalObj eR.inverse _
  have h5 : Nat.card (Idem X.obj)=5 :=
    (hR.terminal_idem_card X ⟨EffectiveFork.terminalFork⟩ hX
      EffectiveFork.terminalFork_isTerminal).trans EffectiveFork.terminal_idem_card
  let eS := splittingEquivalenceOfRestriction e hF hG
  have hS : PreservesRestriction eS.functor := hF.splitFunctor_rst
  let Y := EnumerableCarriers.inclusion_rst.totalFunctor.obj
    (⟨EnumerableCarriers.terminalCarrier⟩ : EnumerableCarriers.Total)
  have hY : IsTerminal Y := EnumerableCarriers.terminalIsTerminal.isTerminalObj
    EnumerableCarriers.inclusion_rst.totalEquivalence.functor _
  have h2 : Nat.card (Idem Y.obj)=2 :=
    (EnumerableCarriers.inclusion_rst.terminal_idem_card
      ⟨EnumerableCarriers.terminalCarrier⟩ Y EnumerableCarriers.terminalIsTerminal hY).symm.trans
      EnumerableCarriers.terminal_idem_card
  have hc := hS.terminal_idem_card X Y hX hY
  rw [h5,h2] at hc
  norm_num at hc

end CategoricalEssentialIncompleteness.LocalConnectedness
