/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EffectiveForkRecursion
public import CategoricalEssentialIncompleteness.EffectiveForkEncoding
public import CategoricalEssentialIncompleteness.RestrictionSplitting

/-! # The restriction splitting recovers all computational forks -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork.Recursion

theorem domain_inclusion_support {X : Object} (e : Idem X) :
    domainInclusion e ≫ e.hom=domainInclusion e := by
  rw [← retraction_inclusion e,← Category.assoc,inclusion_retraction,Category.id_comp]

theorem domain_retraction_support {X : Object} (e : Idem X) :
    e.hom ≫ domainRetraction e=domainRetraction e := by
  rw [← retraction_inclusion e,Category.assoc,inclusion_retraction,Category.comp_id]

abbrev realizeObject (X : SplitObject Rec) : Object := domainObject (toIdem X.domain)

def realizeMap {X Y : SplitObject Rec} (f : X ⟶ Y) : realizeObject X ⟶ realizeObject Y :=
  domainInclusion (toIdem X.domain) ≫ f.hom.hom ≫ domainRetraction (toIdem Y.domain)

def extendMap {X Y : SplitObject Rec} (f : realizeObject X ⟶ realizeObject Y) : X ⟶ Y where
  hom := ObjectProperty.homMk (domainRetraction (toIdem X.domain) ≫ f ≫
    domainInclusion (toIdem Y.domain))
  source := ObjectProperty.hom_ext _ (by
    change (toIdem X.domain).hom ≫ (domainRetraction (toIdem X.domain) ≫ f ≫
      domainInclusion (toIdem Y.domain))=_
    rw [← Category.assoc,domain_retraction_support]
    rfl)
  target := ObjectProperty.hom_ext _ (by
    change (domainRetraction (toIdem X.domain) ≫ f ≫ domainInclusion (toIdem Y.domain)) ≫
      (toIdem Y.domain).hom=_
    rw [Category.assoc,Category.assoc,domain_inclusion_support]
    rfl)

theorem realize_extend {X Y : SplitObject Rec} (f : realizeObject X ⟶ realizeObject Y) :
    realizeMap (extendMap f)=f := by
  change domainInclusion _ ≫ (domainRetraction _ ≫ f ≫ domainInclusion _) ≫ domainRetraction _=f
  rw [← Category.assoc,← Category.assoc,inclusion_retraction,Category.id_comp,
    Category.assoc,inclusion_retraction,Category.comp_id]

theorem extend_realize {X Y : SplitObject Rec} (f : X ⟶ Y) :
    extendMap (realizeMap f)=f := by
  apply SplitObject.Hom.ext
  apply ObjectProperty.hom_ext
  change domainRetraction _ ≫ (domainInclusion _ ≫ f.hom.hom ≫ domainRetraction _) ≫
    domainInclusion _=f.hom.hom
  rw [← Category.assoc,← Category.assoc,retraction_inclusion,Category.assoc,
    Category.assoc,retraction_inclusion]
  have hs : (toIdem X.domain).hom ≫ f.hom.hom=f.hom.hom :=
    congrArg (fun k => k.hom) f.source
  have ht : f.hom.hom ≫ (toIdem Y.domain).hom=f.hom.hom :=
    congrArg (fun k => k.hom) f.target
  rw [← Category.assoc,hs,ht]

def realization : SplitObject Rec ⥤ Object where
  obj := realizeObject
  map := realizeMap
  map_id X := by
    change domainInclusion (toIdem X.domain) ≫ (toIdem X.domain).hom ≫
      domainRetraction (toIdem X.domain)=𝟙 _
    rw [← Category.assoc,domain_inclusion_support,inclusion_retraction]
  map_comp {X Y Z} f g := by
    change domainInclusion _ ≫ (f.hom.hom ≫ g.hom.hom) ≫ domainRetraction _=
      (domainInclusion _ ≫ f.hom.hom ≫ domainRetraction _) ≫
        (domainInclusion _ ≫ g.hom.hom ≫ domainRetraction _)
    have ht : f.hom.hom ≫ (toIdem Y.domain).hom=f.hom.hom :=
      congrArg (fun k => k.hom) f.target
    simp only [Category.assoc]
    rw [← Category.assoc (domainRetraction _),retraction_inclusion,
      ← Category.assoc f.hom.hom (toIdem Y.domain).hom,ht]

instance : realization.Faithful where
  map_injective {X Y} f g h := by
    change realizeMap f=realizeMap g at h
    have hh := congrArg (fun k => extendMap (X := X) (Y := Y) k) h
    simpa only [extend_realize] using hh

instance : realization.Full where
  map_surjective f := ⟨extendMap f,realize_extend f⟩

theorem supported_retraction_domain {X Y : SplitObject Rec} (f : X ⟶ Y) :
    rst (f.hom.hom ≫ domainRetraction (toIdem Y.domain))=rst f.hom.hom := by
  have ht : f.hom.hom ≫ (toIdem Y.domain).hom=f.hom.hom :=
    congrArg (fun k => k.hom) f.target
  have hh : (f.hom.hom ≫ domainRetraction (toIdem Y.domain)) ≫
      domainInclusion (toIdem Y.domain)=f.hom.hom := by
    rw [Category.assoc,retraction_inclusion,ht]
  have h := congrArg rst hh
  rwa [rst_comp_of_isTotal _ (domainInclusion_total (toIdem Y.domain))] at h

/-- The equivalence preserves the restriction operation, not only composition. -/
theorem realization_rst {X Y : SplitObject Rec} (f : X ⟶ Y) :
    realization.map (rst f)=rst (realization.map f) := by
  have h := congrArg (fun k => k ≫ domainRetraction (toIdem X.domain))
    (rst_comp (domainInclusion (toIdem X.domain)) f.hom.hom)
  have he : domainInclusion (toIdem X.domain) ≫ rst f.hom.hom ≫
      domainRetraction (toIdem X.domain)=
        rst (domainInclusion (toIdem X.domain) ≫ f.hom.hom) := by
    simpa only [Category.assoc,inclusion_retraction,Category.comp_id] using h.symm
  change domainInclusion (toIdem X.domain) ≫ (rst f.hom).hom ≫
    domainRetraction (toIdem X.domain)=rst (realizeMap f)
  rw [restriction_hom,he]
  symm
  change rst (domainInclusion (toIdem X.domain) ≫
    (f.hom.hom ≫ domainRetraction (toIdem Y.domain)))=_
  calc
    _=rst (domainInclusion (toIdem X.domain) ≫
        rst (f.hom.hom ≫ domainRetraction (toIdem Y.domain))) := rst_comp_rst_right _ _
    _=rst (domainInclusion (toIdem X.domain) ≫ rst f.hom.hom) := by
      rw [supported_retraction_domain]
    _=_ := (rst_comp_rst_right _ _).symm

theorem realization_essentially_surjective (Y : Object) :
    ∃ X : SplitObject Rec, Nonempty (realization.obj X ≅ Y) := by
  obtain ⟨m,r,_,hmr,hrm⟩ := dominance Y
  let e : Idem V := Idem.ofRestrict r
  let X : SplitObject Rec := ⟨U,ofIdem e⟩
  have he : e.hom=r ≫ m := hrm.symm
  let f : realizeObject X ⟶ Y := domainInclusion e ≫ r
  let g : Y ⟶ realizeObject X := m ≫ domainRetraction e
  refine ⟨X,⟨⟨f,g,?_,?_⟩⟩⟩
  · change (domainInclusion e ≫ r) ≫ (m ≫ domainRetraction e)=𝟙 _
    rw [Category.assoc,← Category.assoc r,← he,← Category.assoc,
      domain_inclusion_support,inclusion_retraction]
  · change (m ≫ domainRetraction e) ≫ (domainInclusion e ≫ r)=𝟙 _
    rw [Category.assoc,← Category.assoc (domainRetraction e),retraction_inclusion]
    change m ≫ rst r ≫ r=𝟙 Y
    rw [rst_comp_self,hmr]

instance : realization.EssSurj := ⟨realization_essentially_surjective⟩

instance : realization.IsEquivalence where

def splittingEquivalence : SplitObject Rec ≌ Object := realization.asEquivalence

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork.Recursion
