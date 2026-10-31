/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnumerableLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Numerical images are stable under total pullbacks -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

def singletonTotal : Total := ⟨terminalCarrier⟩

def point {X : Total} (x : ℕ) (hx : x ∈ X.obj.support) : singletonTotal ⟶ X :=
  ⟨totalFromFunction (fun _ => x) (.const x) (fun _ _ => hx),
    totalFromFunction_total (fun _ => x) (.const x) (fun _ _ => hx)⟩

theorem point_value {X : Total} (x : ℕ) (hx : x ∈ X.obj.support) (n : ℕ)
    (hn : n ∈ terminalCarrier.support) : val (point x hx).hom n=Part.some x :=
  Part.eq_some_iff.mpr ((mem_totalFromFunction (fun _ => x) (.const x)
    (fun _ _ => hx) n x).mpr ⟨hn,rfl⟩)

theorem point_comp_eq {X Y Z : Total} (f : X ⟶ Z) (g : Y ⟶ Z) (x y z : ℕ)
    (hx : x ∈ X.obj.support) (hy : y ∈ Y.obj.support)
    (hf : z ∈ val f.hom x) (hg : z ∈ val g.hom y) :
    point x hx ≫ f=point y hy ≫ g := by
  apply WideSubcategory.hom_ext
  apply val_ext_on_source
  intro n hn
  change val ((point x hx).hom ≫ f.hom) n=val ((point y hy).hom ≫ g.hom) n
  rw [val_comp,val_comp,point_value x hx n hn,point_value y hy n hn,
    Part.bind_some,Part.bind_some]
  exact (Part.eq_some_iff.mpr hf).trans (Part.eq_some_iff.mpr hg).symm

theorem pullback_lifts_elements {P X Y Z : Total} {p : P ⟶ X} {q : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback p q f g) (x y z : ℕ)
    (hf : z ∈ val f.hom x) (hg : z ∈ val g.hom y) :
    ∃ w,x ∈ val p.hom w ∧ y ∈ val q.hom w := by
  have hx := val_source f.hom x z hf
  have hy := val_source g.hom y z hg
  let he := point_comp_eq f g x y z hx hy hf hg
  let u := h.lift (point x hx) (point y hy) he
  obtain ⟨w,hw⟩ := Part.dom_iff_mem.mp ((total_iff u.hom).mp u.property 0 rfl)
  have one {A : Total} (k : P ⟶ A) (a : ℕ) (ha : a ∈ A.obj.support)
      (hk : u ≫ k=point a ha) : a ∈ val k.hom w := by
    have hm : a ∈ val (u ≫ k).hom 0 := by
      rw [hk,point_value a ha 0 rfl]
      exact Part.mem_some _
    obtain ⟨w',hw',ha⟩ := (mem_val_comp u.hom k.hom 0 a).mp hm
    exact Part.mem_unique hw' hw ▸ ha
  exact ⟨w,one p x hx (h.lift_fst _ _ he),one q y hy (h.lift_snd _ _ he)⟩

/-- The component form of regular-image stability, for every total pullback. -/
theorem pullback_image {P X Y Z : Total} {p : P ⟶ X} {q : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback p q f g) :
    Ranges.range q.hom=Idem.pull g.hom (Ranges.range f.hom) := by
  apply support_injective
  ext y
  rw [support_range,support_pull,support_range]
  constructor
  · rintro ⟨w,hq⟩
    obtain ⟨x,hp⟩ := Part.dom_iff_mem.mp ((total_iff p.hom).mp p.property w
      (val_source q.hom w y hq))
    obtain ⟨z,hf⟩ := Part.dom_iff_mem.mp ((total_iff f.hom).mp f.property x
      (val_target p.hom w x hp))
    have hm : z ∈ val (q.hom ≫ g.hom) w := by
      have hw : p.hom ≫ f.hom=q.hom ≫ g.hom := congrArg (fun k => k.hom) h.w
      rw [← hw]
      exact (mem_val_comp p.hom f.hom w z).mpr ⟨x,hp,hf⟩
    obtain ⟨y',hq',hg⟩ := (mem_val_comp q.hom g.hom w z).mp hm
    have he := Part.mem_unique hq' hq
    subst y'
    exact ⟨z,hg,x,hf⟩
  · rintro ⟨z,hg,x,hf⟩
    obtain ⟨w,_,hq⟩ := pullback_lifts_elements h x y z hf hg
    exact ⟨w,hq⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers
