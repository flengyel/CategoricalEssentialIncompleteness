/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerTotalProducts

/-! # Uniform partial inverses on semidecidable images -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.Miller.Total

variable {P : Uniform.Family}

def Injective {X Y : Carrier P} (f : X ⟶ Y) : Prop :=
  ∀ x x' y : ℕ, y ∈ val f x → y ∈ val f x' → x = x'

theorem partialMono_of_injective {X Y : Carrier P} (f : X ⟶ Y) (hf : Injective f) :
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

theorem exists_inverse {X Y : Carrier P} (f : X ⟶ Y) (hf : Injective f) :
    ∃ s : Y ⟶ X,∀ y x : ℕ,x ∈ val s y ↔ y ∈ val f x := by
  let k := Uniform.inverse f.hom hf
  have hk (y x : ℕ) : x ∈ k.val y ↔ y ∈ val f x := Uniform.inverse_graph f.hom hf y x
  let s : Y ⟶ X := arrow k.val k.represented
    (fun y x h => val_target f x y ((hk y x).mp h))
    (fun y x h => val_source f x y ((hk y x).mp h))
  exact ⟨s,hk⟩

theorem inverse_comp {X Y : Carrier P} (f : X ⟶ Y) (s : Y ⟶ X)
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

theorem inverse_receives {X Y : Carrier P} (f : X ⟶ Y) (s : Y ⟶ X)
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

theorem mono_of_total_injective {X Y : Carrier P} (f : X ⟶ Y)
    (hf : isTotal f) (hi : Injective f) : Mono f where
  right_cancellation g h he := by
    have hh := partialMono_of_injective f hi g h he
    simpa only [show rst f = 𝟙 X from hf,Category.comp_id] using hh

def Surjective {X Y : Carrier P} (f : X ⟶ Y) : Prop :=
  ∀ y ∈ Y.support,∃ x,y ∈ val f x

theorem surjective_iff_range_top {X Y : Carrier P} (f : X ⟶ Y) :
    Surjective f ↔ Ranges.range f = ⊤ := by
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

def singletonCarrier : Carrier P := ⟨{0},Uniform.Enumerable.of_re
  ((Primrec.eq.comp Primrec.id (Primrec.const 0)).computablePred.to_re)⟩

def constantPoint {X : Carrier P} (x : ℕ) (hx : x ∈ X.support) : singletonCarrier ⟶ X :=
  totalFromFunction (fun _ => x) (.const x) (fun _ _ => hx)

theorem constantPoint_value {X : Carrier P} (x : ℕ) (hx : x ∈ X.support) :
    val (constantPoint x hx) 0 = Part.some x :=
  Part.eq_some_iff.mpr ((mem_totalFromFunction (fun _ => x) (.const x)
    (fun _ _ => hx) 0 x).mpr ⟨rfl,rfl⟩)

theorem injective_of_partialMono {X Y : Carrier P} (f : X ⟶ Y) (hf : PartialMono f) : Injective f := by
  intro x x' y hy hy'
  let hx := val_source f x y hy
  let hx' := val_source f x' y hy'
  let u := constantPoint x hx
  let v := constantPoint x' hx'
  have he : u ≫ f = v ≫ f := by
    apply val_ext_on_source
    intro n hn
    have hn0 : n=0 := hn
    subst n
    rw [val_comp,val_comp,constantPoint_value,constantPoint_value,Part.bind_some,Part.bind_some]
    exact (Part.eq_some_iff.mpr hy).trans (Part.eq_some_iff.mpr hy').symm
  have hr := congrArg (fun k => val k 0) (hf u v he)
  change (val u 0).bind (val (rst f)) = (val v 0).bind (val (rst f)) at hr
  rw [constantPoint_value,constantPoint_value,Part.bind_some,Part.bind_some] at hr
  have ha : val (rst f) x = Part.some x :=
    Part.eq_some_iff.mpr ((mem_val_restriction f x x).mpr ⟨⟨y,hy⟩,rfl⟩)
  have hb : val (rst f) x' = Part.some x' :=
    Part.eq_some_iff.mpr ((mem_val_restriction f x' x').mpr ⟨⟨y,hy'⟩,rfl⟩)
  rw [ha,hb] at hr
  exact Part.some_injective hr

instance : WeakChoice (Carrier P) where
  section_exists f hf := by
    obtain ⟨s,hs⟩ := exists_inverse f (injective_of_partialMono f hf)
    exact ⟨s,inverse_comp f s hs,inverse_receives f s hs⟩

end CategoricalEssentialIncompleteness.V46.Miller.Total
