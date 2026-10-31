/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnumerableRegular
import Mathlib.CategoryTheory.Types.Basic

/-! # Underlying sets of total recursive c.e. carrier maps -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

def totalFunction {X Y : Total} (f : X ⟶ Y) (x : {n // n ∈ X.obj.support}) :
    {n // n ∈ Y.obj.support} :=
  ⟨(val f.hom x.val).get ((total_iff f.hom).mp f.property x.val x.property),
    val_target f.hom _ _ (Part.get_mem _)⟩

theorem totalFunction_mem {X Y : Total} (f : X ⟶ Y) (x : {n // n ∈ X.obj.support}) :
    (totalFunction f x).val ∈ val f.hom x.val := Part.get_mem _

def underlying : Total ⥤ Type where
  obj X := {n // n ∈ X.obj.support}
  map f := ↾(totalFunction f)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact ((mem_supportIdentity X.obj.support x.val _).mp (totalFunction_mem (𝟙 X) x)).2
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact Part.mem_unique (totalFunction_mem (f ≫ g) x)
      ((mem_val_comp f.hom g.hom _ _).mpr
        ⟨_,totalFunction_mem f x,totalFunction_mem g (totalFunction f x)⟩)

theorem totalFunction_eq_iff {X Y : Total} (f : X ⟶ Y)
    (x : {n // n ∈ X.obj.support}) (y : {n // n ∈ Y.obj.support}) :
    underlying.map f x=y ↔ y.val ∈ val f.hom x.val := by
  constructor
  · intro h
    exact congrArg Subtype.val h ▸ totalFunction_mem f x
  · intro h
    apply Subtype.ext
    exact Part.mem_unique (totalFunction_mem f x) h

instance underlying_reflectsIsomorphisms : underlying.ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    letI := hf
    have hb := (CategoryTheory.isIso_iff_bijective (underlying.map f)).mp inferInstance
    have hi : Injective f.hom := by
      intro x x' y hy hy'
      let a : {n // n ∈ X.obj.support} := ⟨x,val_source f.hom x y hy⟩
      let a' : {n // n ∈ X.obj.support} := ⟨x',val_source f.hom x' y hy'⟩
      have he : underlying.map f a=underlying.map f a' := by
        apply Subtype.ext
        exact (Part.mem_unique (totalFunction_mem f a) hy).trans
          (Part.mem_unique (totalFunction_mem f a') hy').symm
      exact congrArg Subtype.val (hb.1 he)
    have hs : Surjective f.hom := by
      intro y hy
      obtain ⟨x,hx⟩ := hb.2 ⟨y,hy⟩
      refine ⟨x.val,?_⟩
      have he := congrArg Subtype.val hx
      change (totalFunction f x).val=y at he
      rw [← he]
      exact totalFunction_mem f x
    obtain ⟨s,hsg⟩ := exists_inverse f.hom hi
    have st : isTotal s := by
      apply (total_iff s).mpr
      intro y hy
      obtain ⟨x,hx⟩ := hs y hy
      exact Part.dom_iff_mem.mpr ⟨x,(hsg y x).mpr hx⟩
    letI : Mono f.hom := mono_of_total_injective f.hom f.property hi
    have hsf : s ≫ f.hom=𝟙 Y.obj := (inverse_comp f.hom s hsg).trans st
    have hfs : f.hom ≫ s=𝟙 X.obj := by
      apply (cancel_mono f.hom).mp
      rw [Category.assoc,inverse_receives f.hom s hsg,Category.id_comp]
    refine ⟨⟨⟨s,st⟩,?_,?_⟩⟩
    · apply WideSubcategory.hom_ext
      exact hfs
    · apply WideSubcategory.hom_ext
      exact hsf

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers
