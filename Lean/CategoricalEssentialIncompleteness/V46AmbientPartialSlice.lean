/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RestrictionSubobjects

/-! # Partial morphisms over a fixed object in a restriction category -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.AmbientPartialSlice

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]

/-- A total family over the parameter object T. -/
structure Family (T : C) where
  base : C
  proj : base ⟶ T
  total : isTotal proj

variable {T : C}

@[ext] structure Hom (X Y : Family T) where
  hom : X.base ⟶ Y.base
  over : hom ≫ Y.proj = rst hom ≫ X.proj

theorem comp_over {X Y Z : Family T} (f : Hom X Y) (g : Hom Y Z) :
    (f.hom ≫ g.hom) ≫ Z.proj = rst (f.hom ≫ g.hom) ≫ X.proj := by
  calc
    _ = f.hom ≫ (rst g.hom ≫ Y.proj) := by rw [Category.assoc, g.over]
    _ = (rst (f.hom ≫ g.hom) ≫ f.hom) ≫ Y.proj := by
      rw [← Category.assoc, ← rst_comp]
    _ = (rst (f.hom ≫ g.hom) ≫ rst f.hom) ≫ X.proj := by
      rw [Category.assoc, f.over, ← Category.assoc]
    _ = _ := by rw [rst_comm (f.hom ≫ g.hom) f.hom, rst_comp_absorb]

instance familyCategory : Category.{v} (Family T) where
  Hom := Hom
  id X := ⟨𝟙 X.base, by rw [rst_id, Category.id_comp]⟩
  comp f g := ⟨f.hom ≫ g.hom, comp_over f g⟩
  id_comp f := Hom.ext (Category.id_comp f.hom)
  comp_id f := Hom.ext (Category.comp_id f.hom)
  assoc f g h := Hom.ext (Category.assoc f.hom g.hom h.hom)

@[simp] theorem id_hom (X : Family T) : (𝟙 X : X ⟶ X).hom = 𝟙 X.base := rfl

@[simp] theorem comp_hom {X Y Z : Family T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

def restriction {X Y : Family T} (f : X ⟶ Y) : X ⟶ X :=
  ⟨rst f.hom, by rw [restrict_restrict]⟩

instance familyRestriction : RestrictionCategory (Family T) where
  rst := restriction
  rst_comp_self f := Hom.ext (rst_comp_self f.hom)
  rst_comm f g := Hom.ext (rst_comm f.hom g.hom)
  rst_comp_rst f g := Hom.ext (rst_comp_rst f.hom g.hom)
  rst_comp f g := Hom.ext (rst_comp f.hom g.hom)

@[simp] theorem restriction_hom {X Y : Family T} (f : X ⟶ Y) :
    (rst f).hom = rst f.hom := rfl

theorem total_iff {X Y : Family T} (f : X ⟶ Y) :
    isTotal f ↔ isTotal f.hom := by
  constructor
  · intro h
    exact congrArg Hom.hom h
  · intro h
    exact Hom.ext h

def forget : Family T ⥤ C where
  obj X := X.base
  map f := f.hom

instance forget_faithful : (forget (T := T)).Faithful where
  map_injective h := Hom.ext h

theorem forget_restriction {X Y : Family T} (f : X ⟶ Y) :
    (forget (T := T)).map (rst f) = rst ((forget (T := T)).map f) := rfl

def terminalFamily (T : C) : Family T := ⟨T, 𝟙 T, rst_id T⟩

def terminate (X : Family T) : X ⟶ terminalFamily T :=
  ⟨X.proj, by
    change X.proj ≫ 𝟙 T = rst X.proj ≫ X.proj
    rw [Category.comp_id, rst_comp_self]⟩

theorem terminate_total (X : Family T) : isTotal (terminate X) :=
  (total_iff _).mpr X.total

theorem terminate_self : terminate (terminalFamily T) = 𝟙 (terminalFamily T) :=
  Hom.ext rfl

theorem terminate_naturality {X Y : Family T} (f : X ⟶ Y) :
    f ≫ terminate Y = rst f ≫ terminate X := Hom.ext f.over

theorem terminate_unique {X : Family T} (f : X ⟶ terminalFamily T) (hf : isTotal f) :
    f = terminate X := by
  dsimp only [terminalFamily] at f hf
  apply Hom.ext
  have h := f.over
  change f.hom ≫ 𝟙 T = rst f.hom ≫ X.proj at h
  rw [Category.comp_id, show rst f.hom = 𝟙 X.base from (total_iff f).mp hf,
    Category.id_comp] at h
  exact h

end CategoricalEssentialIncompleteness.V46.AmbientPartialSlice
