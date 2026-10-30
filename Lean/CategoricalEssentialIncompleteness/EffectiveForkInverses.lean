/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EffectiveForkSplitting
import CategoricalEssentialIncompleteness.EnumerableInverses

/-! # Natural partial inverses of componentwise injections -/

noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val)

def Injective {X Y : Object} (f : X ⟶ Y) : Prop :=
  EnumerableCarriers.Injective f.center ∧ EnumerableCarriers.Injective f.left ∧
    EnumerableCarriers.Injective f.right

theorem partialMono_of_injective {X Y : Object} (f : X ⟶ Y) (hf : Injective f) :
    PartialMono f := by
  intro W g h he
  exact Hom.ext
    (EnumerableCarriers.partialMono_of_injective f.center hf.1 g.center h.center
      (congrArg Hom.center he))
    (EnumerableCarriers.partialMono_of_injective f.left hf.2.1 g.left h.left
      (congrArg Hom.left he))
    (EnumerableCarriers.partialMono_of_injective f.right hf.2.2 g.right h.right
      (congrArg Hom.right he))

theorem respects_inverse {C A D B : Carrier} {r : C ⟶ A} {s : D ⟶ B}
    {f : C ⟶ D} {g : A ⟶ B} (h : Respects r s f g)
    (f' : D ⟶ C) (g' : B ⟶ A)
    (hf : ∀ y x, x ∈ val f' y ↔ y ∈ val f x)
    (hg : ∀ v u, u ∈ val g' v ↔ v ∈ val g u) : Respects s r f' g' := by
  intro y x v u hyx hyv hxu
  exact (hg v u).mpr (h x y u v ((hf y x).mp hyx) hxu hyv)

theorem exists_inverse {X Y : Object} (f : X ⟶ Y) (hf : Injective f) :
    ∃ s : Y ⟶ X,
      (∀ y x, x ∈ val s.center y ↔ y ∈ val f.center x) ∧
      (∀ y x, x ∈ val s.left y ↔ y ∈ val f.left x) ∧
      (∀ y x, x ∈ val s.right y ↔ y ∈ val f.right x) := by
  obtain ⟨sc, hc⟩ := EnumerableCarriers.exists_inverse f.center hf.1
  obtain ⟨sl, hl⟩ := EnumerableCarriers.exists_inverse f.left hf.2.1
  obtain ⟨sr, hr⟩ := EnumerableCarriers.exists_inverse f.right hf.2.2
  exact ⟨⟨sc, sl, sr, respects_inverse f.natural_left sc sl hc hl,
    respects_inverse f.natural_right sc sr hc hr⟩, hc, hl, hr⟩

theorem section_of_injective {X Y : Object} (f : X ⟶ Y) (hf : Injective f) :
    ∃ s : Y ⟶ X, SectionOf f s := by
  obtain ⟨s, hc, hl, hr⟩ := exists_inverse f hf
  exact ⟨s, ⟨Hom.ext (EnumerableCarriers.inverse_comp f.center s.center hc)
    (EnumerableCarriers.inverse_comp f.left s.left hl)
    (EnumerableCarriers.inverse_comp f.right s.right hr),
    Hom.ext (EnumerableCarriers.inverse_receives f.center s.center hc)
      (EnumerableCarriers.inverse_receives f.left s.left hl)
      (EnumerableCarriers.inverse_receives f.right s.right hr)⟩⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
