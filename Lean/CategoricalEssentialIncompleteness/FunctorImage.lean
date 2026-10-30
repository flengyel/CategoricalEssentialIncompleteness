/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.RangeFunctor

/-! # The extensional image of a functor -/

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms zero_comp comp_zero)

namespace CategoricalEssentialIncompleteness.LocalConnectedness

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

structure FunctorImage (F : C ⥤ D) where
  base : C

namespace FunctorImage

variable (F : C ⥤ D)

@[ext] structure Hom (X Y : FunctorImage F) where
  val : F.obj X.base ⟶ F.obj Y.base
  represented : ∃ f : X.base ⟶ Y.base, F.map f = val

def representative {X Y : FunctorImage F} (f : Hom F X Y) : X.base ⟶ Y.base :=
  Classical.choose f.represented

@[simp] theorem map_representative {X Y : FunctorImage F} (f : Hom F X Y) :
    F.map (representative F f) = f.val := Classical.choose_spec f.represented

instance : Category (FunctorImage F) where
  Hom := Hom F
  id X := ⟨𝟙 _, ⟨𝟙 X.base, F.map_id X.base⟩⟩
  comp f g := ⟨f.val ≫ g.val,
    ⟨representative F f ≫ representative F g, by simp⟩⟩
  id_comp f := Hom.ext (Category.id_comp f.val)
  comp_id f := Hom.ext (Category.comp_id f.val)
  assoc f g h := Hom.ext (Category.assoc f.val g.val h.val)

def quotient : C ⥤ FunctorImage F where
  obj X := ⟨X⟩
  map f := ⟨F.map f, ⟨f, rfl⟩⟩
  map_id X := Hom.ext (F.map_id X)
  map_comp f g := Hom.ext (F.map_comp f g)

def inclusion : FunctorImage F ⥤ D where
  obj X := F.obj X.base
  map f := f.val

instance : (inclusion F).Faithful where
  map_injective h := Hom.ext h

theorem quotient_map_surjective (X Y : C) :
    Function.Surjective (fun f : X ⟶ Y => (quotient F).map f) := by
  intro f
  obtain ⟨g, hg⟩ := f.represented
  exact ⟨g, Hom.ext hg⟩

theorem quotient_inclusion : quotient F ⋙ inclusion F = F := rfl

variable [RestrictionCategory C] [RestrictionCategory D]

def restriction (hr : ∀ {X Y : C} (f : X ⟶ Y), F.map (rst f) = rst (F.map f))
    {X Y : FunctorImage F} (f : X ⟶ Y) : X ⟶ X :=
  ⟨rst f.val, ⟨rst (representative F f), by rw [hr, map_representative]⟩⟩

def restrictionCategory (hr : ∀ {X Y : C} (f : X ⟶ Y), F.map (rst f) = rst (F.map f)) :
    RestrictionCategory (FunctorImage F) where
  rst := restriction F hr
  rst_comp_self f := Hom.ext (rst_comp_self f.val)
  rst_comm f g := Hom.ext (rst_comm f.val g.val)
  rst_comp_rst f g := Hom.ext (rst_comp_rst f.val g.val)
  rst_comp f g := Hom.ext (rst_comp f.val g.val)

end FunctorImage

end CategoricalEssentialIncompleteness.LocalConnectedness
