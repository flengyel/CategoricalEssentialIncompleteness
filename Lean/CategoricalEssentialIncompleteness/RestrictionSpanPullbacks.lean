/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.RestrictionSpans
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Pullback composition of monic spans -/

@[expose] public section

universe v u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.PartialSpans

variable {C : Type u} [Category.{v} C] [RestrictionCategory C] [Splits C]
  [WeakChoice C] [Ranges C]

/-- A total pullback also lifts partial cones with the same restriction domain. -/
theorem partial_pullback_lift {P A B Z : Total C}
    {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ Z} {g : B ⟶ Z}
    (hp : IsPullback fst snd f g) {W : C} (a : W ⟶ A.obj) (b : W ⟶ B.obj)
    (hd : rst a=rst b) (he : a ≫ f.hom=b ≫ g.hom) :
    ∃ h : W ⟶ P.obj, h ≫ fst.hom=a ∧ h ≫ snd.hom=b ∧ rst h=rst a := by
  obtain ⟨D,m,r,hm,hmr,hrm⟩ := Splits.splitting (Idem.ofRestrict a)
  change r ≫ m=rst a at hrm
  have hma : m ≫ rst a=m := by rw [← hrm, ← Category.assoc,hmr,Category.id_comp]
  have hab : isTotal (m ≫ a) := by
    change rst (m ≫ a)=𝟙 D
    rw [rst_comp_rst_right,hma]
    exact hm
  have hbb : isTotal (m ≫ b) := by
    change rst (m ≫ b)=𝟙 D
    rw [rst_comp_rst_right,← hd,hma]
    exact hm
  let a' : (⟨D⟩ : Total C) ⟶ A := ⟨m ≫ a,hab⟩
  let b' : (⟨D⟩ : Total C) ⟶ B := ⟨m ≫ b,hbb⟩
  have he' : a' ≫ f=b' ≫ g := by
    apply WideSubcategory.hom_ext
    change (m ≫ a) ≫ f.hom=(m ≫ b) ≫ g.hom
    simp only [Category.assoc,he]
  let l := hp.lift a' b' he'
  have hlf : l.hom ≫ fst.hom=m ≫ a := congrArg (fun k => k.hom) (hp.lift_fst a' b' he')
  have hls : l.hom ≫ snd.hom=m ≫ b := congrArg (fun k => k.hom) (hp.lift_snd a' b' he')
  refine ⟨r ≫ l.hom,?_,?_,?_⟩
  · rw [Category.assoc,hlf,← Category.assoc,hrm,rst_comp_self]
  · rw [Category.assoc,hls,← Category.assoc,hrm,hd,rst_comp_self]
  · rw [rst_comp_of_isTotal r l.property]
    have hh := congrArg rst hrm
    rwa [rst_comp_of_isTotal r hm,restrict_restrict] at hh

theorem inverse_pullback_snd {A B Z : Total C} (f : A ⟶ Z) (g : B ⟶ Z)
    [Mono g] [HasPullback f g] :
    inverse (pullback.fst f g) ≫ (pullback.snd f g).hom=f.hom ≫ inverse g := by
  let p := f.hom ≫ inverse g
  have hcond : rst p ≫ f.hom=p ≫ g.hom := by
    dsimp [p]
    rw [rst_comp,Category.assoc,inverse_hom]
  obtain ⟨h,hf,hs,hr⟩ := partial_pullback_lift (IsPullback.of_hasPullback f g)
    (rst p) p (restrict_restrict p) hcond
  have hp : (pullback.fst f g).hom ≫ p=(pullback.snd f g).hom := by
    dsimp [p]
    rw [← Category.assoc,← WideSubcategory.comp_def,pullback.condition,
      WideSubcategory.comp_def,Category.assoc,hom_inverse,Category.comp_id]
  have hh : SectionOf (pullback.fst f g).hom h := by
    constructor
    · exact hf.trans (hr.trans (restrict_restrict p)).symm
    · rw [← Category.assoc,Category.assoc _ h,hf]
      have he := rst_comp (pullback.fst f g).hom p
      rw [hp,show rst (pullback.snd f g).hom=𝟙 _ from (pullback.snd f g).property,
        Category.id_comp] at he
      exact he.symm
  have hinv := PartialMono.section_unique (partialMono_of_mono (pullback.fst f g))
    (inverse_section _) hh
  rw [hinv]
  exact hs

def Span.pullbackComp {X Y Z : C} (s : Span X Y) (t : Span Y Z)
    [HasPullback s.map t.mono] : Span X Z where
  apex := pullback s.map t.mono
  mono := pullback.fst s.map t.mono ≫ s.mono
  map := pullback.snd s.map t.mono ≫ t.map

theorem Span.value_pullbackComp {X Y Z : C} (s : Span X Y) (t : Span Y Z)
    [HasPullback s.map t.mono] : (s.pullbackComp t).value=s.value ≫ t.value := by
  change inverse (pullback.fst s.map t.mono ≫ s.mono) ≫
    ((pullback.snd s.map t.mono).hom ≫ t.map.hom)=_
  rw [inverse_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (inverse (pullback.fst s.map t.mono)),inverse_pullback_snd]
  simp only [Span.value,Category.assoc]

/-- Composition of the span classes is the usual pullback composition. -/
theorem pullback_composition {X Y Z : C} (s : Span X Y) (t : Span Y Z)
    [HasPullback s.map t.mono] :
    s.toHom ≫ t.toHom = (s.pullbackComp t).toHom := by
  apply (homEquiv X Z).injective
  change homEquiv X Z ((homEquiv X Z).symm (s.value ≫ t.value))=_
  rw [Equiv.apply_symm_apply]
  exact (s.value_pullbackComp t).symm

end CategoricalEssentialIncompleteness.LocalConnectedness.PartialSpans
