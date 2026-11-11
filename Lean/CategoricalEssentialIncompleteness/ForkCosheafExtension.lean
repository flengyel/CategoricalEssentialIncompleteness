/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkCosheafCoequalizer
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-! # The actual pushout extension of a set-valued fork -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology

def basisFunctor : WalkingSpan ⥤ Open := span (homOfLE Open.d_le_l) (homOfLE Open.d_le_r)

def restrict (F : Open ⥤ Type) : WalkingSpan ⥤ Type := basisFunctor ⋙ F

def extensionValue (Y : WalkingSpan ⥤ Type) : Open → Type
  | .empty => Empty
  | .D => Y.obj .zero
  | .L => Y.obj .left
  | .R => Y.obj .right
  | .whole => pushout (Y.map WalkingSpan.Hom.fst) (Y.map WalkingSpan.Hom.snd)

def extensionArrow (Y : WalkingSpan ⥤ Type) :
    (U V : Open) → U ≤ V → (extensionValue Y U ⟶ extensionValue Y V)
  | .empty,_,_ => ↾fun x => Empty.elim x
  | .D,.D,_ => 𝟙 _
  | .D,.L,_ => Y.map WalkingSpan.Hom.fst
  | .D,.R,_ => Y.map WalkingSpan.Hom.snd
  | .D,.whole,_ => Y.map WalkingSpan.Hom.fst ≫ pushout.inl _ _
  | .L,.L,_ => 𝟙 _
  | .L,.whole,_ => pushout.inl _ _
  | .R,.R,_ => 𝟙 _
  | .R,.whole,_ => pushout.inr _ _
  | .whole,.whole,_ => 𝟙 _
  | .D,.empty,h => False.elim ((by decide : ¬ Open.D ≤ .empty) h)
  | .L,.empty,h => False.elim ((by decide : ¬ Open.L ≤ .empty) h)
  | .R,.empty,h => False.elim ((by decide : ¬ Open.R ≤ .empty) h)
  | .whole,.empty,h => False.elim ((by decide : ¬ Open.whole ≤ .empty) h)
  | .L,.D,h => False.elim ((by decide : ¬ Open.L ≤ .D) h)
  | .L,.R,h => False.elim ((by decide : ¬ Open.L ≤ .R) h)
  | .R,.D,h => False.elim ((by decide : ¬ Open.R ≤ .D) h)
  | .R,.L,h => False.elim ((by decide : ¬ Open.R ≤ .L) h)
  | .whole,.D,h => False.elim ((by decide : ¬ Open.whole ≤ .D) h)
  | .whole,.L,h => False.elim ((by decide : ¬ Open.whole ≤ .L) h)
  | .whole,.R,h => False.elim ((by decide : ¬ Open.whole ≤ .R) h)

def extension (Y : WalkingSpan ⥤ Type) : Open ⥤ Type where
  obj := extensionValue Y
  map {U V} f := extensionArrow Y U V (leOfHom f)
  map_id U := by
    cases U
    · apply ConcreteCategory.hom_ext
      intro x
      exact Empty.elim x
    all_goals rfl
  map_comp {U V W} f g := by
    have hf := leOfHom f
    have hg := leOfHom g
    cases U <;> cases V <;> cases W
    all_goals simp [Open.le_cases] at hf hg
    all_goals simp [extensionArrow,pushout.condition]
    all_goals
      apply ConcreteCategory.hom_ext
      intro x
      exact Empty.elim x

def extension_empty_initial (Y : WalkingSpan ⥤ Type) : IsInitial ((extension Y).obj .empty) :=
  IsInitial.ofUniqueHom (fun _ => ↾fun x => Empty.elim x)
    (by intro B f; apply ConcreteCategory.hom_ext; intro x; exact Empty.elim x)

theorem extension_cosheaf (Y : WalkingSpan ⥤ Type) : IsCosheaf (extension Y) :=
  cosheaf_of_pushout _ (extension_empty_initial Y)
    (IsPushout.of_hasPushout (Y.map WalkingSpan.Hom.fst) (Y.map WalkingSpan.Hom.snd))

/-- In particular, the whole-space value is an actual set pushout. -/
theorem extension_whole (Y : WalkingSpan ⥤ Type) :
    (extension Y).obj .whole=pushout (Y.map WalkingSpan.Hom.fst) (Y.map WalkingSpan.Hom.snd) := rfl

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology
