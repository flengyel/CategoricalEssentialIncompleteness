/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EnumerableChoice
public import CategoricalEssentialIncompleteness.EnumerableCoproducts
public import CategoricalEssentialIncompleteness.LocalSwitch

/-! # Local connectedness, splitting and weak choice for c.e. numerical carriers -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

theorem singleton_connected {X : Carrier} (x : ℕ) (hx : x ∈ X.support) :
    Connected (singletonIdem x hx) := by
  intro b c he hd
  have hm : x ∈ support (b ⊔ c) := by
    rw [← he,support_singletonIdem]
    exact Set.mem_singleton x
  rw [support_sup] at hm
  rcases hm with hb | hc
  · have hs : singletonIdem x hx ≤ b := by
      apply (support_le_iff _ _).mpr
      rw [support_singletonIdem]
      exact Set.singleton_subset_iff.mpr hb
    have hcb : c ≤ b := le_trans (by rw [he]; exact le_sup_right) hs
    exact Or.inr ((inf_eq_right.mpr hcb).symm.trans hd)
  · have hs : singletonIdem x hx ≤ c := by
      apply (support_le_iff _ _).mpr
      rw [support_singletonIdem]
      exact Set.singleton_subset_iff.mpr hc
    have hbc : b ≤ c := le_trans (by rw [he]; exact le_sup_left) hs
    exact Or.inl ((inf_eq_left.mpr hbc).symm.trans hd)

instance : LocallyConnected Carrier where
  hom_ext {X Y} f g h := by
    apply val_ext_on_source
    intro x hx
    apply eq_at_of_precomp_idem (singletonIdem x hx) f g
      (h _ (singleton_connected x hx)) x
    rw [support_singletonIdem]
    exact Set.mem_singleton x

instance : Splits Carrier where
  splitting a := ⟨subcarrier a,into a,outof a,into_total a,into_outof a,outof_into a⟩

instance : WeakChoice Carrier where
  section_exists f _ := exists_section f

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers
