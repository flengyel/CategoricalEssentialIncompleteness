/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkCosheafExtension

/-! # Natural maps of pushout extensions -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology

def extensionComponent {Y Z : WalkingSpan ⥤ Type} (a : Y ⟶ Z) :
    (U : Open) → extensionValue Y U ⟶ extensionValue Z U
  | .empty => ↾fun x => Empty.elim x
  | .D => a.app .zero
  | .L => a.app .left
  | .R => a.app .right
  | .whole => pushout.map (Y.map WalkingSpan.Hom.fst) (Y.map WalkingSpan.Hom.snd)
      (Z.map WalkingSpan.Hom.fst) (Z.map WalkingSpan.Hom.snd)
      (a.app .left) (a.app .right) (a.app .zero)
      (a.naturality WalkingSpan.Hom.fst) (a.naturality WalkingSpan.Hom.snd)

def extensionNat {Y Z : WalkingSpan ⥤ Type} (a : Y ⟶ Z) : extension Y ⟶ extension Z where
  app := extensionComponent a
  naturality {U V} f := by
    have hf := leOfHom f
    have hl := a.naturality WalkingSpan.Hom.fst
    have hr := a.naturality WalkingSpan.Hom.snd
    cases U <;> cases V
    all_goals simp [Open.le_cases] at hf
    all_goals simp [extension,extensionArrow,extensionComponent,pushout.map,Category.assoc,
      hl,hr,reassoc_of% hl,reassoc_of% hr]
    all_goals
      apply ConcreteCategory.hom_ext
      intro x
      exact Empty.elim x

theorem extensionNat_id (Y : WalkingSpan ⥤ Type) : extensionNat (𝟙 Y)=𝟙 (extension Y) := by
  apply NatTrans.ext
  funext U
  cases U
  all_goals simp [extension,extensionValue,extensionNat,extensionComponent,pushout.map_id]
  apply ConcreteCategory.hom_ext
  intro x
  exact Empty.elim x

theorem extensionNat_comp {Y Z W : WalkingSpan ⥤ Type} (a : Y ⟶ Z) (b : Z ⟶ W) :
    extensionNat (a ≫ b)=extensionNat a ≫ extensionNat b := by
  apply NatTrans.ext
  funext U
  cases U
  all_goals try rfl
  · apply ConcreteCategory.hom_ext
    intro x
    exact Empty.elim x
  · apply pushout.hom_ext
    all_goals simp [extensionNat,extensionComponent,pushout.map,Category.assoc]

def extensionPresheafFunctor : (WalkingSpan ⥤ Type) ⥤ (Open ⥤ Type) where
  obj := extension
  map := extensionNat
  map_id := extensionNat_id
  map_comp := extensionNat_comp

def restrictExtensionIso (Y : WalkingSpan ⥤ Type) : Y ≅ restrict (extension Y) :=
  spanIsoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [restrict,basisFunctor,extension,extensionArrow])
    (by simp [restrict,basisFunctor,extension,extensionArrow])

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology
