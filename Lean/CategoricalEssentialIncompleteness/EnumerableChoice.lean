/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnumerableInverses

/-! # Computable preimage choice on c.e. numerical carriers -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

open ClassicalPrograms

def Surjective {X Y : Carrier} (f : X ⟶ Y) : Prop :=
  ∀ y ∈ Y.support,∃ x,y ∈ val f x

theorem surjective_iff_range_top {X Y : Carrier} (f : X ⟶ Y) :
    Surjective f ↔ Ranges.range f=⊤ := by
  constructor
  · intro h
    apply support_injective
    rw [support_range,support_top]
    exact Set.Subset.antisymm (fun _ ⟨x,hx⟩ => val_target f x _ hx) h
  · intro h y hy
    have hh := congrArg support h
    rw [support_range,support_top] at hh
    rw [← hh] at hy
    exact hy

/-- Numerical preimage search chooses one inverse value; no injectivity is required. -/
theorem exists_section {X Y : Carrier} (f : X ⟶ Y) : ∃ s : Y ⟶ X,SectionOf f s := by
  obtain ⟨s,hs⟩ := CategoryTheory.HasChoice.exists_isSection f.hom
  have hc := congrArg (fun k => J.map k) hs.comp_eq_rst
  change J.map (s ≫ f.hom)=J.map (rst s) at hc
  rw [J.map_comp,J_rst] at hc
  have hr := congrArg (fun k => J.map k) hs.comp_self
  rw [J.map_comp,J.map_comp] at hr
  have sound (y x : ℕ) (h : x ∈ J.map s y) : y ∈ val f x := by
    have hh : y ∈ (J.map s ≫ J.map f.hom) y := by
      rw [hc]
      exact (PartialFunctions.mem_rst _ y y).mpr ⟨⟨x,h⟩,rfl⟩
    obtain ⟨x',hx',hy⟩ := (PartialFunctions.mem_comp _ _ y y).mp hh
    exact Part.mem_unique hx' h ▸ hy
  let s' : Y ⟶ X := arrow (J.map s) (omegaArrow_partrec s)
    (fun y x h => val_target f x y (sound y x h))
    (fun y x h => val_source f x y (sound y x h))
  refine ⟨s',?_,?_⟩
  · apply val_injective
    rw [val_restriction]
    change J.map s ≫ J.map f.hom=PartialFunctions.restriction (J.map s)
    exact hc
  · apply val_injective
    exact hr

theorem surjective_section {X Y : Carrier} (f : X ⟶ Y) (hf : Surjective f) :
    ∃ s : Y ⟶ X,isTotal s ∧ s ≫ f=𝟙 Y := by
  obtain ⟨s,hs⟩ := exists_section f
  have he : Idem.ofRestrict s=⊤ := hs.domain.trans ((surjective_iff_range_top f).mp hf)
  have ht : isTotal s := congrArg Idem.hom he
  exact ⟨s,ht,hs.comp.trans ht⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers
