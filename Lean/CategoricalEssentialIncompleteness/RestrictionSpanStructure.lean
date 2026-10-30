/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.RestrictionSpanPullbacks

/-! # Restriction structure on monic-span classes -/

universe v u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.PartialSpans

variable {C : Type u} [Category.{v} C] [RestrictionCategory C] [Splits C]
  [WeakChoice C] [Ranges C]

def parRst {X Y : Par C} (f : X ⟶ Y) : X ⟶ X :=
  (homEquiv X.obj X.obj).symm (rst (comparison.map f))

@[simp] theorem comparison_parRst {X Y : Par C} (f : X ⟶ Y) :
    comparison.map (parRst f)=rst (comparison.map f) :=
  (homEquiv X.obj X.obj).apply_symm_apply _

instance parRestriction : RestrictionCategory (Par C) where
  rst := parRst
  rst_comp_self f := by
    apply (homEquiv _ _).injective
    change comparison.map (parRst f ≫ f)=comparison.map f
    rw [comparison.map_comp,comparison_parRst,rst_comp_self]
  rst_comm f g := by
    apply (homEquiv _ _).injective
    change comparison.map (parRst f ≫ parRst g)=comparison.map (parRst g ≫ parRst f)
    simp only [comparison.map_comp,comparison_parRst]
    exact rst_comm _ _
  rst_comp_rst f g := by
    apply (homEquiv _ _).injective
    change comparison.map (parRst (parRst f ≫ g))=comparison.map (parRst f ≫ parRst g)
    simp only [comparison.map_comp,comparison_parRst]
    exact rst_comp_rst _ _
  rst_comp f g := by
    apply (homEquiv _ _).injective
    change comparison.map (parRst (f ≫ g) ≫ f)=comparison.map (f ≫ parRst g)
    simp only [comparison.map_comp,comparison_parRst]
    exact rst_comp _ _

theorem comparison_rst {X Y : Par C} (f : X ⟶ Y) :
    comparison.map (rst f)=rst (comparison.map f) := comparison_parRst f

theorem comparison_toHom {X Y : C} (s : Span X Y) :
    comparison.map s.toHom=s.value := rfl

def Span.restriction {X Y : C} (s : Span X Y) : Span X X :=
  ⟨s.apex,s.mono,s.mono,inferInstance⟩

/-- Restriction is the span with both legs equal to the domain inclusion. -/
theorem Span.restriction_toHom {X Y : C} (s : Span X Y) :
    s.restriction.toHom=rst s.toHom := by
  apply (homEquiv X X).injective
  change comparison.map s.restriction.toHom=comparison.map (rst s.toHom)
  rw [comparison_rst,comparison_toHom,comparison_toHom]
  exact (inverse_hom s.mono).trans s.restrict_value.symm

def identitySpan (X : C) : Span X X :=
  ⟨⟨X⟩,𝟙 _,𝟙 _,inferInstance⟩

theorem identity_span (X : C) : (identitySpan X).toHom=𝟙 (Par.mk X) := by
  apply (homEquiv X X).injective
  change comparison.map (identitySpan X).toHom=comparison.map (𝟙 (Par.mk X))
  rw [comparison.map_id,comparison_toHom]
  change inverse (𝟙 (⟨X⟩ : Total C)) ≫ 𝟙 X=𝟙 X
  have h := hom_inverse (𝟙 (⟨X⟩ : Total C))
  simpa only [WideSubcategory.id_def,Category.id_comp,Category.comp_id] using h

end CategoricalEssentialIncompleteness.LocalConnectedness.PartialSpans
