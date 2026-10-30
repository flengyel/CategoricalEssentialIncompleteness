/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnumerablePCategory

/-! # Computable partial inverses on c.e. images -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

open ClassicalPrograms

def Injective {X Y : Carrier} (f : X ⟶ Y) : Prop :=
  ∀ x x' y : ℕ, y ∈ val f x → y ∈ val f x' → x = x'

theorem partialMono_of_injective {X Y : Carrier} (f : X ⟶ Y) (hf : Injective f) :
    PartialMono f := by
  intro W g h he
  have one (g h : W ⟶ X) (he : g ≫ f = h ≫ f) (x z : ℕ)
      (hz : z ∈ val (g ≫ rst f) x) : z ∈ val (h ≫ rst f) x := by
    obtain ⟨a, ha, har⟩ := (mem_val_comp _ _ x z).mp hz
    obtain ⟨⟨b, hb⟩, hza⟩ := (mem_val_restriction f a z).mp har
    have hh : b ∈ val (h ≫ f) x := by
      rw [← he]
      exact (mem_val_comp _ _ x b).mpr ⟨a, ha, hb⟩
    obtain ⟨a', ha', hb'⟩ := (mem_val_comp _ _ x b).mp hh
    have he' : a' = a := hf a' a b hb' hb
    subst a'
    exact (mem_val_comp _ _ x z).mpr ⟨a, ha',
      (mem_val_restriction f a z).mpr ⟨⟨b, hb⟩, hza⟩⟩
  apply val_injective
  apply PFun.ext
  intro x z
  exact ⟨one g h he x z, one h g he.symm x z⟩

theorem exists_inverse {X Y : Carrier} (f : X ⟶ Y) (hf : Injective f) :
    ∃ s : Y ⟶ X, ∀ y x : ℕ, x ∈ val s y ↔ y ∈ val f x := by
  obtain ⟨s, hs⟩ := CategoryTheory.HasChoice.exists_isSection f.hom
  have hc := congrArg (fun k => J.map k) hs.comp_eq_rst
  change J.map (s ≫ f.hom) = J.map (rst s) at hc
  rw [J.map_comp, J_rst] at hc
  have hr := congrArg (fun k => J.map k) hs.comp_self
  rw [J.map_comp, J.map_comp] at hr
  have sound (y x : ℕ) (h : x ∈ J.map s y) : y ∈ val f x := by
    have hh : y ∈ (J.map s ≫ J.map f.hom) y := by
      rw [hc]
      exact (PartialFunctions.mem_rst _ y y).mpr ⟨⟨x, h⟩, rfl⟩
    obtain ⟨x', hx', hy⟩ := (PartialFunctions.mem_comp _ _ y y).mp hh
    have he : x' = x := Part.mem_unique hx' h
    exact he ▸ hy
  have complete (y x : ℕ) (h : y ∈ val f x) : x ∈ J.map s y := by
    have hh : y ∈ (J.map f.hom ≫ J.map s ≫ J.map f.hom) x := by
      rw [hr]
      exact h
    obtain ⟨y', hy', hx⟩ := (PartialFunctions.mem_comp _ _ x y).mp hh
    have he : y' = y := Part.mem_unique hy' h
    subst y'
    obtain ⟨x', hx', hy⟩ := (PartialFunctions.mem_comp _ _ y y).mp hx
    have he : x' = x := hf x' x y hy h
    exact he ▸ hx'
  let inverseArrow : Y ⟶ X := arrow (J.map s) (omegaArrow_partrec s)
    (fun y x h => val_target f x y (sound y x h))
    (fun y x h => val_source f x y (sound y x h))
  exact ⟨inverseArrow, fun y x => ⟨sound y x, complete y x⟩⟩

theorem inverse_comp {X Y : Carrier} (f : X ⟶ Y) (s : Y ⟶ X)
    (h : ∀ y x, x ∈ val s y ↔ y ∈ val f x) : s ≫ f = rst s := by
  apply val_injective
  apply PFun.ext
  intro y z
  simp only [mem_val_comp, mem_val_restriction]
  constructor
  · rintro ⟨x, hyx, hxz⟩
    exact ⟨⟨x, hyx⟩, Part.mem_unique hxz ((h y x).mp hyx)⟩
  · rintro ⟨⟨x, hyx⟩, he⟩
    subst z
    exact ⟨x, hyx, (h y x).mp hyx⟩

theorem inverse_receives {X Y : Carrier} (f : X ⟶ Y) (s : Y ⟶ X)
    (h : ∀ y x, x ∈ val s y ↔ y ∈ val f x) : f ≫ s ≫ f = f := by
  apply val_injective
  apply PFun.ext
  intro x z
  simp only [mem_val_comp]
  constructor
  · rintro ⟨y, hxy, x', hyx', hx'z⟩
    have he : z = y := Part.mem_unique hx'z ((h y x').mp hyx')
    exact he.symm ▸ hxy
  · intro hxz
    exact ⟨z, hxz, x, (h z x).mpr hxz, hxz⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers
