/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.RestrictionFunctorEquivalences

/-! # Totality and total extensions under a restriction functor retraction -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.RestrictionRetraction

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
variable [RestrictionCategory A] [RestrictionCategory B]
variable (F : A ⥤ B) (G : B ⥤ A) (e : F ⋙ G ≅ 𝟭 A)

def recover {X Y : A} (g : F.obj X ⟶ F.obj Y) : X ⟶ Y :=
  e.inv.app X ≫ G.map g ≫ e.hom.app Y

omit [RestrictionCategory A] [RestrictionCategory B] in
theorem recover_map {X Y : A} (f : X ⟶ Y) : recover F G e (F.map f) = f := by
  have h : G.map (F.map f) ≫ e.hom.app Y = e.hom.app X ≫ f := e.hom.naturality f
  calc
    _ = e.inv.app X ≫ (G.map (F.map f) ≫ e.hom.app Y) := rfl
    _ = e.inv.app X ≫ (e.hom.app X ≫ f) := congrArg (fun k => e.inv.app X ≫ k) h
    _ = f := by rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

omit [RestrictionCategory A] [RestrictionCategory B] in
include G e in
theorem faithful : F.Faithful where
  map_injective {X Y} f g h := by
    rw [← recover_map F G e f, ← recover_map F G e g, h]

variable (hF : PreservesRestriction F) (hG : PreservesRestriction G)

include G e hF in
theorem total_iff {X Y : A} (f : X ⟶ Y) : isTotal (F.map f) ↔ isTotal f := by
  let := faithful F G e
  exact ⟨hF.reflects_total f, hF.total f⟩

/-- A total morphism extends a partial morphism when it agrees on its
restriction domain. -/
def HasTotalExtension {D : Type u₁} [Category.{v₁} D] [RestrictionCategory D]
    {X Y : D} (f : X ⟶ Y) : Prop :=
  ∃ g : X ⟶ Y, isTotal g ∧ rst f ≫ g = f

include hG in
theorem recover_total {X Y : A} (g : F.obj X ⟶ F.obj Y) (hg : isTotal g) :
    isTotal (recover F G e g) :=
  isTotal_comp (iso_total (e.app X).symm)
    (isTotal_comp (hG.total g hg) (iso_total (e.app Y)))

include hF in
theorem map_extension {X Y : A} (f : X ⟶ Y) (hf : HasTotalExtension f) :
    HasTotalExtension (F.map f) := by
  obtain ⟨g, hg, hfg⟩ := hf
  refine ⟨F.map g, hF.total g hg, ?_⟩
  rw [← hF f, ← F.map_comp, hfg]

include G e hF hG in
theorem recover_extension {X Y : A} (f : X ⟶ Y) (g : F.obj X ⟶ F.obj Y)
    (hg : isTotal g) (hfg : rst (F.map f) ≫ g = F.map f) :
    isTotal (recover F G e g) ∧ rst f ≫ recover F G e g = f := by
  refine ⟨recover_total F G e hG g hg, ?_⟩
  have hd : rst f ≫ e.inv.app X = e.inv.app X ≫ G.map (F.map (rst f)) :=
    e.inv.naturality (rst f)
  calc
    _ = (rst f ≫ e.inv.app X) ≫ G.map g ≫ e.hom.app Y := by
      simp only [recover, Category.assoc]
    _ = (e.inv.app X ≫ G.map (F.map (rst f))) ≫ G.map g ≫ e.hom.app Y := by rw [hd]
    _ = e.inv.app X ≫ G.map (F.map (rst f) ≫ g) ≫ e.hom.app Y := by
      rw [G.map_comp]
      simp only [Category.assoc]
    _ = recover F G e (F.map f) := by rw [hF f, hfg]; rfl
    _ = f := recover_map F G e f

include G e hF hG in
theorem hasTotalExtension_iff {X Y : A} (f : X ⟶ Y) :
    HasTotalExtension (F.map f) ↔ HasTotalExtension f := by
  refine ⟨?_, map_extension F hF f⟩
  rintro ⟨g, hg, hfg⟩
  exact ⟨recover F G e g, recover_extension F G e hF hG f g hg hfg⟩

include G e hF hG in
theorem noTotalExtension_iff {X Y : A} (f : X ⟶ Y) :
    ¬ HasTotalExtension (F.map f) ↔ ¬ HasTotalExtension f :=
  not_congr (hasTotalExtension_iff F G e hF hG f)

end CategoricalEssentialIncompleteness.V46.RestrictionRetraction
