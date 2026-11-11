/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkProofPresentation
public import CategoricalEssentialIncompleteness.EffectiveForkRecursion

/-! # Essential incompleteness of the actual fork proof theory -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness

namespace EffectiveFork.Recursion

/-- Fullness transfers separators back to the generated recursion category.
The pair itself is the diagonal pair proved inseparable by local lifting. -/
theorem image_pair_inseparable : Inseparable (toIdem pair0) (toIdem pair1) := by
  let e := idemOrderIso U
  constructor
  · change e pair0 ⊓ e pair1=⊥
    rw [← e.map_inf,pair_inseparable.disjoint,e.map_bot]
  · rintro ⟨c,c',hc,ha,hb⟩
    have hcomp : Complementary (e.symm c) (e.symm c') := by
      constructor
      · rw [← e.symm.map_inf,hc.disjoint,e.symm.map_bot]
      · rw [← e.symm.map_sup,hc.cover,e.symm.map_top]
    exact pair_inseparable.no_separator ⟨e.symm c,e.symm c',hcomp,
      e.symm.monotone ha,e.symm.monotone hb⟩

end EffectiveFork.Recursion

namespace ForkSyntax

open EffectiveFork.Recursion (toIdem pair0 pair1)

def categoricalTheory : Idem S := t0 (toIdem pair0) (toIdem pair1)

theorem categoricalTheory_consistent :
    categoricalTheory ⊓ Idem.pull nu categoricalTheory=⊥ :=
  t0_consistency _ _ EffectiveFork.Recursion.image_pair_inseparable.disjoint

/-- The three-point application of Corollary 6.7, using the actual Turing
diagonal pair, finite proof object and conclusion range. -/
theorem essential_incompleteness (t : Idem S) (ht : categoricalTheory ≤ t)
    (hconsistent : t ⊓ Idem.pull nu t=⊥) :
    Inseparable t (Idem.pull nu t) ∧ t ⊔ Idem.pull nu t≠⊤ :=
  domain_incompleteness EffectiveFork.Recursion.image_pair_inseparable
    theta theta_total nu nu_total categoricalTheory
    (positive_inclusion _ _) (negative_inclusion _ _) t ht hconsistent

theorem categoricalTheory_inseparable :
    Inseparable categoricalTheory (Idem.pull nu categoricalTheory) :=
  (essential_incompleteness categoricalTheory le_rfl categoricalTheory_consistent).1

theorem categoricalTheory_incomplete :
    categoricalTheory ⊔ Idem.pull nu categoricalTheory≠⊤ :=
  (essential_incompleteness categoricalTheory le_rfl categoricalTheory_consistent).2

end ForkSyntax
end CategoricalEssentialIncompleteness.LocalConnectedness
