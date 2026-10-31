/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.ForkCosheafExamples
import CategoricalEssentialIncompleteness.ForkObstruction
import CategoricalEssentialIncompleteness.RestrictionFunctorEquivalences
import CategoricalEssentialIncompleteness.EffectiveForkIdempotents
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # The actual terminal numerical and fork domain lattices have two and five elements -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness

namespace EnumerableCarriers

theorem terminal_support_mem (a : Idem terminalCarrier) (x : ℕ) :
    x ∈ support a ↔ x=0 ∧ 0 ∈ support a := by
  constructor
  · intro h
    have he : x=0 := support_subset a h
    exact ⟨he,he ▸ h⟩
  · rintro ⟨rfl,h⟩
    exact h

def terminalIdemEquiv : Idem terminalCarrier ≃ Bool where
  toFun a := decide (0 ∈ support a)
  invFun b := if b then ⊤ else ⊥
  left_inv a := by
    apply support_injective
    ext x
    by_cases h : 0 ∈ support a
    · simp only [h,decide_true,Bool.true_eq,ite_true,support_top]
      change x=0 ↔ x ∈ support a
      simpa only [h,and_true] using (terminal_support_mem a x).symm
    · simp only [h,decide_false,Bool.false_eq_true,ite_false,support_bot,Set.mem_empty_iff_false]
      exact (terminal_support_mem a x).trans (by simp [h]) |>.symm
  right_inv b := by cases b <;> simp [support_top,support_bot,terminalCarrier]

theorem terminal_idem_card : Nat.card (Idem terminalCarrier)=2 :=
  (Nat.card_congr terminalIdemEquiv).trans (by simp [Nat.card_eq_fintype_card])

end EnumerableCarriers

namespace EffectiveFork

def terminalFork : Object := fromDiagram ForkTopology.Examples.T

def terminalFork_isTerminal : IsTerminal (⟨terminalFork⟩ : Total) :=
  ForkTopology.Examples.T_terminal.isTerminalObj totalEquivalence.inverse _

def terminalPattern (a : Idem terminalFork) : Fork.TerminalSupport :=
  ⟨(EnumerableCarriers.terminalIdemEquiv (centerIdem a),
    EnumerableCarriers.terminalIdemEquiv (leftIdem a),
    EnumerableCarriers.terminalIdemEquiv (rightIdem a)),by
    intro hc
    have hc' : 0 ∈ EnumerableCarriers.support (centerIdem a) := of_decide_eq_true hc
    constructor
    · apply decide_eq_true
      apply closed_left a 0 0 hc'
      exact (mem_supportIdentity _ 0 0).mpr ⟨rfl,rfl⟩
    · apply decide_eq_true
      apply closed_right a 0 0 hc'
      exact (mem_supportIdentity _ 0 0).mpr ⟨rfl,rfl⟩⟩

def patternIdem (p : Fork.TerminalSupport) : Idem terminalFork :=
  identityOn (EnumerableCarriers.terminalIdemEquiv.symm p.val.1)
    (EnumerableCarriers.terminalIdemEquiv.symm p.val.2.1)
    (EnumerableCarriers.terminalIdemEquiv.symm p.val.2.2)
    (by
      intro x u hx hu
      have hx0 : x=0 := EnumerableCarriers.support_subset _ hx
      have hu0 : u=0 := EnumerableCarriers.val_target terminalFork.leftMap x u hu
      subst x
      subst u
      have hc : p.val.1=true := by
        have h := EnumerableCarriers.terminalIdemEquiv.apply_symm_apply p.val.1
        change decide (0 ∈ EnumerableCarriers.support
          (EnumerableCarriers.terminalIdemEquiv.symm p.val.1))=p.val.1 at h
        simpa only [hx,decide_true] using h.symm
      have h := EnumerableCarriers.terminalIdemEquiv.apply_symm_apply p.val.2.1
      change decide (0 ∈ EnumerableCarriers.support
        (EnumerableCarriers.terminalIdemEquiv.symm p.val.2.1))=p.val.2.1 at h
      exact of_decide_eq_true (h.trans (p.property hc).1))
    (by
      intro x u hx hu
      have hx0 : x=0 := EnumerableCarriers.support_subset _ hx
      have hu0 : u=0 := EnumerableCarriers.val_target terminalFork.rightMap x u hu
      subst x
      subst u
      have hc : p.val.1=true := by
        have h := EnumerableCarriers.terminalIdemEquiv.apply_symm_apply p.val.1
        change decide (0 ∈ EnumerableCarriers.support
          (EnumerableCarriers.terminalIdemEquiv.symm p.val.1))=p.val.1 at h
        simpa only [hx,decide_true] using h.symm
      have h := EnumerableCarriers.terminalIdemEquiv.apply_symm_apply p.val.2.2
      change decide (0 ∈ EnumerableCarriers.support
        (EnumerableCarriers.terminalIdemEquiv.symm p.val.2.2))=p.val.2.2 at h
      exact of_decide_eq_true (h.trans (p.property hc).2))

/-- Every closed terminal-support pattern is an actual computably enumerable
partial identity, and every such partial identity has exactly one pattern. -/
def terminalIdemEquiv : Idem terminalFork ≃ Fork.TerminalSupport where
  toFun := terminalPattern
  invFun := patternIdem
  left_inv a := by
    apply idem_ext
    · exact EnumerableCarriers.terminalIdemEquiv.symm_apply_apply (centerIdem a)
    · exact EnumerableCarriers.terminalIdemEquiv.symm_apply_apply (leftIdem a)
    · exact EnumerableCarriers.terminalIdemEquiv.symm_apply_apply (rightIdem a)
  right_inv p := by
    apply Subtype.ext
    change (EnumerableCarriers.terminalIdemEquiv
        (EnumerableCarriers.terminalIdemEquiv.symm p.val.1),
      EnumerableCarriers.terminalIdemEquiv
        (EnumerableCarriers.terminalIdemEquiv.symm p.val.2.1),
      EnumerableCarriers.terminalIdemEquiv
        (EnumerableCarriers.terminalIdemEquiv.symm p.val.2.2))=p.val
    simp only [Equiv.apply_symm_apply]

theorem terminal_idem_card : Nat.card (Idem terminalFork)=5 :=
  (Nat.card_congr terminalIdemEquiv).trans (by
    rw [Nat.card_eq_fintype_card,Fork.terminalSupport_card])

end EffectiveFork
end CategoricalEssentialIncompleteness.LocalConnectedness
