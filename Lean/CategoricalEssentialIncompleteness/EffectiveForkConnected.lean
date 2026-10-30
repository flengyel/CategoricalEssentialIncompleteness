/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EffectiveForkIdempotents

/-! # Finite generating subfunctors and local connectedness -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val singletonIdem)

def centerAtom {X : Object} (x u v : ℕ) (hx : x ∈ X.center.support)
    (hu : u ∈ val X.leftMap x) (hv : v ∈ val X.rightMap x) : Idem X :=
  identityOn (singletonIdem x hx)
    (singletonIdem u (EnumerableCarriers.val_target _ _ _ hu))
    (singletonIdem v (EnumerableCarriers.val_target _ _ _ hv))
    (by
      intro z w hz hw
      rw [EnumerableCarriers.support_singletonIdem] at hz ⊢
      have he : z = x := hz
      subst z
      exact Part.mem_unique hw hu)
    (by
      intro z w hz hw
      rw [EnumerableCarriers.support_singletonIdem] at hz ⊢
      have he : z = x := hz
      subst z
      exact Part.mem_unique hw hv)

theorem centerAtom_le {X : Object} (x u v : ℕ) (hx : x ∈ X.center.support)
    (hu : u ∈ val X.leftMap x) (hv : v ∈ val X.rightMap x)
    (a : Idem X) (ha : x ∈ EnumerableCarriers.support (centerIdem a)) :
    centerAtom x u v hx hu hv ≤ a := by
  apply (idem_le_iff _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply (EnumerableCarriers.support_le_iff _ _).mpr
    change EnumerableCarriers.support (singletonIdem x hx) ⊆ _
    rw [EnumerableCarriers.support_singletonIdem]
    exact Set.singleton_subset_iff.mpr ha
  · apply (EnumerableCarriers.support_le_iff _ _).mpr
    change EnumerableCarriers.support
      (singletonIdem u (EnumerableCarriers.val_target _ _ _ hu)) ⊆ _
    rw [EnumerableCarriers.support_singletonIdem]
    exact Set.singleton_subset_iff.mpr (closed_left a x u ha hu)
  · apply (EnumerableCarriers.support_le_iff _ _).mpr
    change EnumerableCarriers.support
      (singletonIdem v (EnumerableCarriers.val_target _ _ _ hv)) ⊆ _
    rw [EnumerableCarriers.support_singletonIdem]
    exact Set.singleton_subset_iff.mpr (closed_right a x v ha hv)

theorem centerAtom_connected {X : Object} (x u v : ℕ) (hx : x ∈ X.center.support)
    (hu : u ∈ val X.leftMap x) (hv : v ∈ val X.rightMap x) :
    Connected (centerAtom x u v hx hu hv) := by
  intro b c he hd
  have hm : x ∈ EnumerableCarriers.support (centerIdem (b ⊔ c)) := by
    rw [← he]
    change x ∈ EnumerableCarriers.support (singletonIdem x hx)
    rw [EnumerableCarriers.support_singletonIdem]
    exact Set.mem_singleton x
  change x ∈ EnumerableCarriers.support (centerIdem b ⊔ centerIdem c) at hm
  rw [EnumerableCarriers.support_sup] at hm
  rcases hm with hb | hc
  · have hcb : c ≤ b := le_trans (by rw [he]; exact le_sup_right)
      (centerAtom_le x u v hx hu hv b hb)
    exact Or.inr ((inf_eq_right.mpr hcb).symm.trans hd)
  · have hbc : b ≤ c := le_trans (by rw [he]; exact le_sup_left)
      (centerAtom_le x u v hx hu hv c hc)
    exact Or.inl ((inf_eq_left.mpr hbc).symm.trans hd)

def leftAtom {X : Object} (u : ℕ) (hu : u ∈ X.left.support) : Idem X :=
  identityOn ⊥ (singletonIdem u hu) ⊥
    (by intro x z hx; rw [EnumerableCarriers.support_bot] at hx; exact False.elim hx)
    (by intro x z hx; rw [EnumerableCarriers.support_bot] at hx; exact False.elim hx)

def rightAtom {X : Object} (v : ℕ) (hv : v ∈ X.right.support) : Idem X :=
  identityOn ⊥ ⊥ (singletonIdem v hv)
    (by intro x z hx; rw [EnumerableCarriers.support_bot] at hx; exact False.elim hx)
    (by intro x z hx; rw [EnumerableCarriers.support_bot] at hx; exact False.elim hx)

theorem leftAtom_le {X : Object} (u : ℕ) (hu : u ∈ X.left.support)
    (a : Idem X) (ha : u ∈ EnumerableCarriers.support (leftIdem a)) : leftAtom u hu ≤ a := by
  apply (idem_le_iff _ _).mpr
  refine ⟨bot_le, ?_, bot_le⟩
  apply (EnumerableCarriers.support_le_iff _ _).mpr
  change EnumerableCarriers.support (singletonIdem u hu) ⊆ _
  rw [EnumerableCarriers.support_singletonIdem]
  exact Set.singleton_subset_iff.mpr ha

theorem rightAtom_le {X : Object} (v : ℕ) (hv : v ∈ X.right.support)
    (a : Idem X) (ha : v ∈ EnumerableCarriers.support (rightIdem a)) : rightAtom v hv ≤ a := by
  apply (idem_le_iff _ _).mpr
  refine ⟨bot_le, bot_le, ?_⟩
  apply (EnumerableCarriers.support_le_iff _ _).mpr
  change EnumerableCarriers.support (singletonIdem v hv) ⊆ _
  rw [EnumerableCarriers.support_singletonIdem]
  exact Set.singleton_subset_iff.mpr ha

theorem leftAtom_connected {X : Object} (u : ℕ) (hu : u ∈ X.left.support) :
    Connected (leftAtom u hu) := by
  intro b c he hd
  have hm : u ∈ EnumerableCarriers.support (leftIdem (b ⊔ c)) := by
    rw [← he]
    change u ∈ EnumerableCarriers.support (singletonIdem u hu)
    rw [EnumerableCarriers.support_singletonIdem]
    exact Set.mem_singleton u
  change u ∈ EnumerableCarriers.support (leftIdem b ⊔ leftIdem c) at hm
  rw [EnumerableCarriers.support_sup] at hm
  rcases hm with hb | hc
  · have hcb : c ≤ b := le_trans (by rw [he]; exact le_sup_right) (leftAtom_le u hu b hb)
    exact Or.inr ((inf_eq_right.mpr hcb).symm.trans hd)
  · have hbc : b ≤ c := le_trans (by rw [he]; exact le_sup_left) (leftAtom_le u hu c hc)
    exact Or.inl ((inf_eq_left.mpr hbc).symm.trans hd)

theorem rightAtom_connected {X : Object} (v : ℕ) (hv : v ∈ X.right.support) :
    Connected (rightAtom v hv) := by
  intro b c he hd
  have hm : v ∈ EnumerableCarriers.support (rightIdem (b ⊔ c)) := by
    rw [← he]
    change v ∈ EnumerableCarriers.support (singletonIdem v hv)
    rw [EnumerableCarriers.support_singletonIdem]
    exact Set.mem_singleton v
  change v ∈ EnumerableCarriers.support (rightIdem b ⊔ rightIdem c) at hm
  rw [EnumerableCarriers.support_sup] at hm
  rcases hm with hb | hc
  · have hcb : c ≤ b := le_trans (by rw [he]; exact le_sup_right) (rightAtom_le v hv b hb)
    exact Or.inr ((inf_eq_right.mpr hcb).symm.trans hd)
  · have hbc : b ≤ c := le_trans (by rw [he]; exact le_sup_left) (rightAtom_le v hv c hc)
    exact Or.inl ((inf_eq_left.mpr hbc).symm.trans hd)

instance : LocallyConnected Object where
  hom_ext {X Y} f g h := by
    apply Hom.ext
    · apply EnumerableCarriers.val_ext_on_source
      intro x hx
      obtain ⟨u, hu⟩ := Part.dom_iff_mem.mp
        ((EnumerableCarriers.total_iff X.leftMap).mp X.left_total x hx)
      obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp
        ((EnumerableCarriers.total_iff X.rightMap).mp X.right_total x hx)
      let a := centerAtom x u v hx hu hv
      apply EnumerableCarriers.eq_at_of_precomp_idem (centerIdem a) f.center g.center
        (congrArg Hom.center (h a (centerAtom_connected x u v hx hu hv))) x
      change x ∈ EnumerableCarriers.support (singletonIdem x hx)
      rw [EnumerableCarriers.support_singletonIdem]
      exact Set.mem_singleton x
    · apply EnumerableCarriers.val_ext_on_source
      intro u hu
      let a := leftAtom u hu
      apply EnumerableCarriers.eq_at_of_precomp_idem (leftIdem a) f.left g.left
        (congrArg Hom.left (h a (leftAtom_connected u hu))) u
      change u ∈ EnumerableCarriers.support (singletonIdem u hu)
      rw [EnumerableCarriers.support_singletonIdem]
      exact Set.mem_singleton u
    · apply EnumerableCarriers.val_ext_on_source
      intro v hv
      let a := rightAtom v hv
      apply EnumerableCarriers.eq_at_of_precomp_idem (rightIdem a) f.right g.right
        (congrArg Hom.right (h a (rightAtom_connected v hv))) v
      change v ∈ EnumerableCarriers.support (singletonIdem v hv)
      rw [EnumerableCarriers.support_singletonIdem]
      exact Set.mem_singleton v

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
