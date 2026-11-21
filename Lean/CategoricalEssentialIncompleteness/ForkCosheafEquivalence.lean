/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkCosheafExtensionMaps
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering

/-! # Restriction and pushout extension give a cosheaf equivalence -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology

def cosheafProperty : ObjectProperty (Open ⥤ Type) := IsCosheaf

abbrev CoSh := ObjectProperty.FullSubcategory cosheafProperty

def restrictionFunctor : CoSh ⥤ (WalkingSpan ⥤ Type) where
  obj F := restrict F.obj
  map a := Functor.whiskerLeft basisFunctor a.hom

def extensionFunctor : (WalkingSpan ⥤ Type) ⥤ CoSh where
  obj Y := ⟨extension Y,extension_cosheaf Y⟩
  map a := ObjectProperty.homMk (extensionNat a)
  map_id Y := ObjectProperty.hom_ext _ (extensionNat_id Y)
  map_comp a b := ObjectProperty.hom_ext _ (extensionNat_comp a b)

def extensionRestrictionComponent (F : CoSh) : (U : Open) →
    (extension (restrict F.obj)).obj U ≅ F.obj.obj U
  | .empty => (extension_empty_initial _).uniqueUpToIso (cosheaf_empty_initial F.property)
  | .D => Iso.refl _
  | .L => Iso.refl _
  | .R => Iso.refl _
  | .whole => (cosheaf_pushout F.property).isoPushout.symm

def extensionRestrictionNatIso (F : CoSh) : extension (restrict F.obj) ≅ F.obj :=
  NatIso.ofComponents (extensionRestrictionComponent F) (by
    intro U V f
    have hf := leOfHom f
    have hn : f=homOfLE (leOfHom f) := Subsingleton.elim _ _
    rw [hn]
    cases U <;> cases V
    all_goals simp [Open.le_cases] at hf
    all_goals simp [extensionRestrictionComponent,extension,extensionValue,extensionArrow,
      restrict,basisFunctor,Category.assoc,IsPushout.inl_isoPushout_inv,
      IsPushout.inr_isoPushout_inv]
    all_goals
      apply ConcreteCategory.hom_ext
      intro x
      exact Empty.elim x)

def extensionRestrictionIso : restrictionFunctor ⋙ extensionFunctor ≅ 𝟭 CoSh :=
  NatIso.ofComponents (fun F => ObjectProperty.isoMk _ (extensionRestrictionNatIso F)) (by
    intro F G a
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    cases U
    · apply ConcreteCategory.hom_ext
      intro x
      exact Empty.elim x
    · simp [extensionFunctor,restrictionFunctor,extensionNat,extensionComponent,
        extensionRestrictionNatIso,extensionRestrictionComponent,basisFunctor]
    · simp [extensionFunctor,restrictionFunctor,extensionNat,extensionComponent,
        extensionRestrictionNatIso,extensionRestrictionComponent,basisFunctor]
    · simp [extensionFunctor,restrictionFunctor,extensionNat,extensionComponent,
        extensionRestrictionNatIso,extensionRestrictionComponent,basisFunctor]
    · apply pushout.hom_ext
      · simpa [extensionFunctor,restrictionFunctor,extensionNat,extensionComponent,
          extensionRestrictionNatIso,extensionRestrictionComponent,Category.assoc,
          pushout.map,basisFunctor,IsPushout.inl_isoPushout_inv] using
          (a.hom.naturality (homOfLE Open.l_le_whole)).symm
      · simpa [extensionFunctor,restrictionFunctor,extensionNat,extensionComponent,
          extensionRestrictionNatIso,extensionRestrictionComponent,Category.assoc,
          pushout.map,basisFunctor,IsPushout.inr_isoPushout_inv] using
          (a.hom.naturality (homOfLE Open.r_le_whole)).symm)

def restrictionExtensionIso : 𝟭 (WalkingSpan ⥤ Type) ≅
    extensionFunctor ⋙ restrictionFunctor :=
  NatIso.ofComponents restrictExtensionIso (by
    intro Y Z a
    apply NatTrans.ext
    funext j
    rcases j with _ | (_ | _)
    all_goals simp [restrictExtensionIso,extensionFunctor,restrictionFunctor,
      extensionNat,extensionComponent,basisFunctor,restrict])

/-- Proposition B.1: restriction to the three basis opens, with inverse given by the set
pushout at the whole space. -/
def cosheafEquivalence : CoSh ≌ (WalkingSpan ⥤ Type) where
  functor := restrictionFunctor
  inverse := extensionFunctor
  unitIso := extensionRestrictionIso.symm
  counitIso := restrictionExtensionIso.symm
  functor_unitIso_comp F := by
    apply NatTrans.ext
    funext j
    rcases j with _ | (_ | _)
    all_goals simp [extensionRestrictionIso,extensionRestrictionNatIso,
      extensionRestrictionComponent,restrictionExtensionIso,restrictExtensionIso,
      restrictionFunctor,extensionFunctor,basisFunctor,restrict,extension,extensionValue]

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology
