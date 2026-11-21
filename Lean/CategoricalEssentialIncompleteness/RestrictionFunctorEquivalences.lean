/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.RestrictionSplitting
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Restriction equivalences preserve splitting and total categories -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness

universe u v u' v'
variable {C : Type u} [Category.{v} C] [RestrictionCategory C]
  {D : Type u'} [Category.{v'} D] [RestrictionCategory D]

def PreservesRestriction (F : C ⥤ D) : Prop :=
  ∀ {X Y} (f : X ⟶ Y),F.map (rst f)=rst (F.map f)

namespace PreservesRestriction

variable {F : C ⥤ D} (hF : PreservesRestriction F)
include hF

def mapIdem {X : C} (a : Idem X) : Idem (F.obj X) :=
  ⟨F.map a.hom,(hF a.hom).symm.trans (congrArg F.map a.restriction)⟩

theorem total {X Y : C} (f : X ⟶ Y) (hf : isTotal f) : isTotal (F.map f) := by
  rw [isTotal,← hF f,show rst f=𝟙 X from hf,F.map_id]

theorem reflects_total [F.Faithful] {X Y : C} (f : X ⟶ Y)
    (hf : isTotal (F.map f)) : isTotal f := by
  apply F.map_injective
  rw [hF f,show rst (F.map f)=𝟙 _ from hf,F.map_id]

def mapIdemEquiv [F.Full] [F.Faithful] (X : C) : Idem X ≃ Idem (F.obj X) where
  toFun := hF.mapIdem
  invFun a := ⟨F.preimage a.hom,by
    apply F.map_injective
    rw [hF _,F.map_preimage,a.restriction]⟩
  left_inv a := Idem.ext (F.preimage_map a.hom)
  right_inv a := Idem.ext (F.map_preimage a.hom)

def splitFunctor : SplitObject C ⥤ SplitObject D where
  obj X := ⟨F.obj X.base,hF.mapIdem X.domain⟩
  map f := ⟨F.map f.hom,by simpa only [mapIdem,← F.map_comp] using congrArg F.map f.source,
    by simpa only [mapIdem,← F.map_comp] using congrArg F.map f.target⟩
  map_id X := SplitObject.Hom.ext rfl
  map_comp f g := SplitObject.Hom.ext (F.map_comp f.hom g.hom)

theorem splitFunctor_rst : PreservesRestriction hF.splitFunctor := by
  intro X Y f
  exact SplitObject.Hom.ext (hF f.hom)

instance splitFunctor_faithful [F.Faithful] : hF.splitFunctor.Faithful where
  map_injective {X Y} f g he :=
    SplitObject.Hom.ext (F.map_injective (congrArg SplitObject.Hom.hom he))

instance splitFunctor_full [F.Full] [F.Faithful] : hF.splitFunctor.Full where
  map_surjective {X Y} f := by
    let g : X ⟶ Y := ⟨F.preimage f.hom,by
      apply F.map_injective
      simpa only [splitFunctor,mapIdem,F.map_comp,F.map_preimage] using f.source,by
      apply F.map_injective
      simpa only [splitFunctor,mapIdem,F.map_comp,F.map_preimage] using f.target⟩
    exact ⟨g,SplitObject.Hom.ext (F.map_preimage f.hom)⟩

def totalFunctor : WideSubcategory (isTotal (C := C)) ⥤
    WideSubcategory (isTotal (C := D)) where
  obj X := ⟨F.obj X.obj⟩
  map f := ⟨F.map f.hom,hF.total f.hom f.property⟩
  map_id X := by apply WideSubcategory.hom_ext; exact F.map_id X.obj
  map_comp f g := by apply WideSubcategory.hom_ext; exact F.map_comp f.hom g.hom

instance totalFunctor_faithful [F.Faithful] : hF.totalFunctor.Faithful where
  map_injective {X Y} f g he := by
    apply WideSubcategory.hom_ext
    exact F.map_injective (congrArg (fun k => k.hom) he)

instance totalFunctor_full [F.Full] [F.Faithful] : hF.totalFunctor.Full where
  map_surjective f :=
    ⟨⟨F.preimage f.hom,hF.reflects_total _ (by
      rw [F.map_preimage]; exact f.property)⟩,
      by apply WideSubcategory.hom_ext; exact F.map_preimage f.hom⟩

instance totalFunctor_essSurj [F.EssSurj] : hF.totalFunctor.EssSurj where
  mem_essImage Y := by
    let X := F.objPreimage Y.obj
    let i := F.objObjPreimageIso Y.obj
    exact ⟨⟨X⟩,⟨⟨⟨i.hom,iso_total i⟩,⟨i.inv,iso_total i.symm⟩,
      by apply WideSubcategory.hom_ext; exact i.hom_inv_id,
      by apply WideSubcategory.hom_ext; exact i.inv_hom_id⟩⟩⟩

def totalEquivalence [F.IsEquivalence] :
    WideSubcategory (isTotal (C := C)) ≌ WideSubcategory (isTotal (C := D)) := by
  letI : hF.totalFunctor.IsEquivalence := {}
  exact hF.totalFunctor.asEquivalence

def totalInclusion (C : Type u) [Category.{v} C] [RestrictionCategory C] :
    WideSubcategory (isTotal (C := C)) ⥤ C where
  obj X := X.obj
  map f := f.hom


end PreservesRestriction

namespace Idem

def isoEquiv {X Y : C} (i : X ≅ Y) : Idem X ≃ Idem Y where
  toFun := pull i.inv
  invFun := pull i.hom
  left_inv a := by rw [← pull_comp,i.hom_inv_id,pull_id]
  right_inv a := by rw [← pull_comp,i.inv_hom_id,pull_id]

theorem isoEquiv_hom {X Y : C} (i : X ≅ Y) (a : Idem X) :
    (isoEquiv i a).hom=i.inv ≫ a.hom ≫ i.hom := by
  change (pull i.inv a).hom=_
  calc
    _ = ((pull i.inv a).hom ≫ i.inv) ≫ i.hom := by simp
    _ = _ := by rw [pull_commute,Category.assoc]

end Idem

namespace PreservesRestriction

variable {F : C ⥤ D} (hF : PreservesRestriction F)
include hF

/-- The domain cardinality of a total terminal object is invariant under restriction
equivalence, using the full and faithful idempotent map. -/
theorem terminal_idem_card [F.IsEquivalence]
    (X : WideSubcategory (isTotal (C := C)))
    (Y : WideSubcategory (isTotal (C := D)))
    (hX : Limits.IsTerminal X) (hY : Limits.IsTerminal Y) :
    Nat.card (Idem X.obj)=Nat.card (Idem Y.obj) := by
  let e := hF.totalEquivalence
  have hFX : Limits.IsTerminal (hF.totalFunctor.obj X) := hX.isTerminalObj e.functor X
  let i := (totalInclusion D).mapIso (hFX.uniqueUpToIso hY)
  exact (Nat.card_congr (hF.mapIdemEquiv X.obj)).trans (Nat.card_congr (Idem.isoEquiv i))

end PreservesRestriction

/-- An isomorphism that intertwines the two specified domains restricts to
an isomorphism between the corresponding objects of the restriction splitting. -/
def splitIsoOfComm {X Y : SplitObject C} (i : X.base ≅ Y.base)
    (h : X.domain.hom ≫ i.hom=i.hom ≫ Y.domain.hom) : X ≅ Y where
  hom := ⟨X.domain.hom ≫ i.hom,by rw [← Category.assoc,X.domain.idem],by
    rw [h,Category.assoc,Y.domain.idem]⟩
  inv := ⟨i.inv ≫ X.domain.hom,by
    apply (cancel_epi i.hom).mp
    change i.hom ≫ (Y.domain.hom ≫ (i.inv ≫ X.domain.hom))=
      i.hom ≫ (i.inv ≫ X.domain.hom)
    rw [← Category.assoc i.hom,← h]
    simp only [Category.assoc,Iso.hom_inv_id_assoc,X.domain.idem],by
    rw [Category.assoc,X.domain.idem]⟩
  hom_inv_id := SplitObject.Hom.ext (by
    change (X.domain.hom ≫ i.hom) ≫ (i.inv ≫ X.domain.hom)=X.domain.hom
    simp only [Category.assoc,Iso.hom_inv_id_assoc,X.domain.idem])
  inv_hom_id := SplitObject.Hom.ext (by
    change (i.inv ≫ X.domain.hom) ≫ (X.domain.hom ≫ i.hom)=Y.domain.hom
    rw [Category.assoc,← Category.assoc X.domain.hom,X.domain.idem,h,
      ← Category.assoc,i.inv_hom_id,Category.id_comp])

theorem splitFunctor_essSurj_of_equivalence (e : C ≌ D)
    (hF : PreservesRestriction e.functor) (hG : PreservesRestriction e.inverse) :
    hF.splitFunctor.EssSurj where
  mem_essImage Y := by
    let X := hG.splitFunctor.obj Y
    refine ⟨X,⟨splitIsoOfComm (e.counitIso.app Y.base) ?_⟩⟩
    exact e.counitIso.hom.naturality Y.domain.hom

/-- A restriction equivalence induces an equivalence of the restriction splittings;
preservation of other structure is not required for this step. -/
def splittingEquivalenceOfRestriction (e : C ≌ D)
    (hF : PreservesRestriction e.functor) (hG : PreservesRestriction e.inverse) :
    SplitObject C ≌ SplitObject D := by
  letI := splitFunctor_essSurj_of_equivalence e hF hG
  letI : hF.splitFunctor.IsEquivalence := {}
  exact hF.splitFunctor.asEquivalence

end CategoricalEssentialIncompleteness.LocalConnectedness
