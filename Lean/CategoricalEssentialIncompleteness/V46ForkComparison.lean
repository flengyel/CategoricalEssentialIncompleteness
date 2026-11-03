/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46Comparison
import CategoricalEssentialIncompleteness.ForkEssentialIncompleteness

/-! # Complementary conditionals in the generated fork recursion category -/

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct

namespace CategoricalEssentialIncompleteness.LocalConnectedness

namespace EffectiveFork.Recursion

/-- Fullness puts each total target conditional back in the generated
recursion category, with the same restrictions and agreement equations. -/
theorem complementary_conditionals_v46
    (c c' : Idem U) (hc : Complementary c c') :
    ∃ ℓ : U ⟶ coprod U U, isTotal ℓ ∧
      c.hom ≫ ℓ = c.hom ≫ i1 U U ∧
      c'.hom ≫ ℓ = c'.hom ≫ i0 U U := by
  obtain ⟨s, _, hs, h1, h0⟩ := complementary_switch
    (rangeFunctor.mapIdem c) (rangeFunctor.mapIdem c')
    (rangeFunctor.map_complementary hc)
  refine ⟨ObjectProperty.homMk s, ?_, ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    rw [restriction_hom]
    exact hs
  · exact ObjectProperty.hom_ext _ h1
  · exact ObjectProperty.hom_ext _ h0

/-- The actual generated fork diagonal pair follows from Corollary 3.3. -/
theorem pair_inseparable_v46 : Inseparable pair0 pair1 :=
  source_inseparable_of_complementary_conditionals rangeFunctor
    turing turing_isTuring sumFrame inclusion_nonzero complementary_conditionals_v46

/-- The fully faithful inclusion preserves and reflects every possible
separator of the actual diagonal pair. -/
theorem image_pair_inseparable_v46 :
    Inseparable (toIdem pair0) (toIdem pair1) := by
  let e := idemOrderIso U
  constructor
  · change e pair0 ⊓ e pair1 = ⊥
    rw [← e.map_inf, pair_inseparable_v46.disjoint, e.map_bot]
  · rintro ⟨c, c', hc, ha, hb⟩
    have hcomp : Complementary (e.symm c) (e.symm c') := by
      constructor
      · rw [← e.symm.map_inf, hc.disjoint, e.symm.map_bot]
      · rw [← e.symm.map_sup, hc.cover, e.symm.map_top]
    exact pair_inseparable_v46.no_separator
      ⟨e.symm c, e.symm c', hcomp, e.symm.monotone ha, e.symm.monotone hb⟩

end EffectiveFork.Recursion

namespace ForkSyntax

/-- The nonnumerical theory application through Corollaries 3.3 and 4.3,
using the constructed proof-conclusion range and atomic inclusions. -/
theorem essential_incompleteness_v46 (t : Idem S) (ht : categoricalTheory ≤ t)
    (hc : t ⊓ Idem.pull nu t = ⊥) :
    Inseparable t (Idem.pull nu t) ∧ t ⊔ Idem.pull nu t ≠ ⊤ :=
  domain_incompleteness EffectiveFork.Recursion.image_pair_inseparable_v46
    theta theta_total nu nu_total categoricalTheory
    (positive_inclusion _ _) (negative_inclusion _ _) t ht hc

end ForkSyntax

end CategoricalEssentialIncompleteness.LocalConnectedness
