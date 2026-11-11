/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46TranslationGalois
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Generation across first-order presentations

The category of axiom subobjects allows logical translations between
presentations. Its full subcategory of closed theories is reflective.
The hom-set bijection retains the three translation morphisms.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.FirstOrderPresentation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

structure Axioms (V : D) where
  presentation : FirstOrderPresentation V
  axioms : Subobject presentation.syntaxData.sentenceObject

namespace Axioms

variable {V : D}

structure Hom (A B : Axioms V) where
  translation : Translation A.presentation B.presentation
  bound : (Subobject.«exists» translation.sentence).obj A.axioms ≤ B.axioms

namespace Hom

@[ext] theorem ext {A B : Axioms V} {f g : Hom A B}
    (h : f.translation = g.translation) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (A : Axioms V) : Hom A A where
  translation := Translation.id A.presentation
  bound := by
    change (Subobject.«exists» (𝟙 _)).obj A.axioms ≤ A.axioms
    rw [Subobject.exists_iso_map, Subobject.map_id]

def comp {A B C : Axioms V} (f : Hom A B) (g : Hom B C) : Hom A C where
  translation := f.translation.comp g.translation
  bound := by
    change (Subobject.«exists» (f.translation.sentence ≫ g.translation.sentence)).obj
      A.axioms ≤ C.axioms
    rw [Subobject.exists_comp]
    exact (leOfHom ((Subobject.«exists» g.translation.sentence).map
      (homOfLE f.bound))).trans g.bound

end Hom

instance : Category.{v} (Axioms (D := D) V) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by
    apply Hom.ext
    apply Translation.ext <;> simp [Hom.comp, Hom.id, Translation.comp, Translation.id]
  comp_id f := by
    apply Hom.ext
    apply Translation.ext <;> simp [Hom.comp, Hom.id, Translation.comp, Translation.id]
  assoc f g h := by
    apply Hom.ext
    apply Translation.ext <;> simp [Hom.comp, Translation.comp, Category.assoc]

def IsTheory : ObjectProperty (Axioms (D := D) V) := fun A =>
  FirstOrderReflection.generated A.presentation.proofs A.axioms = A.axioms

abbrev TheoryCategory := (IsTheory (D := D) (V := V)).FullSubcategory

@[implicit_reducible]
def inclusion : TheoryCategory (D := D) (V := V) ⥤ Axioms V := IsTheory.ι

instance inclusion_full : (inclusion (D := D) (V := V)).Full :=
  inferInstanceAs (IsTheory.ι.Full)

instance inclusion_faithful : (inclusion (D := D) (V := V)).Faithful :=
  inferInstanceAs (IsTheory.ι.Faithful)

def generationObject (A : Axioms V) : TheoryCategory (D := D) (V := V) :=
  ⟨⟨A.presentation, FirstOrderReflection.generated A.presentation.proofs A.axioms⟩,
    FirstOrderReflection.idempotent A.presentation.proofs A.presentation.initial A.axioms⟩

def generation : Axioms V ⥤ TheoryCategory (D := D) (V := V) where
  obj := generationObject
  map {A B} f := ObjectProperty.homMk {
    translation := f.translation
    bound := f.translation.map_generated_of_le A.axioms B.axioms f.bound }
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply Hom.ext
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply Hom.ext
    rfl

def homEquiv (A : Axioms V) (B : TheoryCategory (D := D) (V := V)) :
    ((generation (D := D) (V := V)).obj A ⟶ B) ≃
      (A ⟶ (inclusion (D := D) (V := V)).obj B) where
  toFun f := {
    translation := f.hom.translation
    bound := (leOfHom ((Subobject.«exists» f.hom.translation.sentence).map
      (homOfLE (FirstOrderReflection.extensive A.presentation.proofs A.axioms)))).trans
        f.hom.bound }
  invFun f := ObjectProperty.homMk {
    translation := f.translation
    bound := by
      have h := f.translation.map_generated_of_le A.axioms B.obj.axioms f.bound
      change (Subobject.«exists» f.translation.sentence).obj
          (FirstOrderReflection.generated A.presentation.proofs A.axioms) ≤
        FirstOrderReflection.generated B.obj.presentation.proofs B.obj.axioms at h
      rw [B.property] at h
      exact h }
  left_inv _ := by
    apply ObjectProperty.hom_ext
    apply Hom.ext
    rfl
  right_inv _ := Hom.ext rfl

theorem homEquiv_translation (A : Axioms V) (B : TheoryCategory (D := D) (V := V))
    (f : (generation.obj A ⟶ B)) :
    (homEquiv A B f).translation = f.hom.translation := rfl

def adjunction : generation (D := D) (V := V) ⊣ inclusion :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm := fun _ _ => by
      apply ObjectProperty.hom_ext
      apply Hom.ext
      rfl
    homEquiv_naturality_right := fun _ _ => Hom.ext rfl }

end Axioms
end CategoricalEssentialIncompleteness.V46.FirstOrderPresentation
