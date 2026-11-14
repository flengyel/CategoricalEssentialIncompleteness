/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSliceChangeBase

/-! # Both adjunctions in the actual monic partial-map slices -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialSliceChangeBase

open RestrictionSubobjects
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [HasPullbacks (Tot C)] {T U : Tot C} (i : T ⟶ U) (inverses : MonoInverses C)

local notation "Eₜ" => PartialSliceEquivalence.functor inverses T
local notation "Eᵤ" => PartialSliceEquivalence.functor inverses U

def leftHomEquiv (X : PartialMaps.Par (Over T)) (Y : PartialMaps.Par (Over U)) :
    ((postcompose i).obj X ⟶ Y) ≃ (X ⟶ (reindex i inverses).obj Y) :=
  ((Functor.FullyFaithful.ofFullyFaithful Eᵤ).homEquiv (X := (postcompose i).obj X) (Y := Y)).trans
    ((PartialSliceLeftAdjunction.homEquiv i ((Eₜ).obj X) ((Eᵤ).obj Y)).trans
      ((Functor.FullyFaithful.ofFullyFaithful Eₜ).homEquiv
        (X := X) (Y := (reindex i inverses).obj Y)).symm)

theorem leftHomEquiv_value {X : PartialMaps.Par (Over T)} {Y : PartialMaps.Par (Over U)}
    (f : (postcompose i).obj X ⟶ Y) :
    (Eₜ).map ((leftHomEquiv i inverses X Y) f) =
      (PartialSliceLeftAdjunction.homEquiv i ((Eₜ).obj X) ((Eᵤ).obj Y)) ((Eᵤ).map f) :=
  (Eₜ).map_preimage _

theorem leftHomEquiv_symm_value {X : PartialMaps.Par (Over T)} {Y : PartialMaps.Par (Over U)}
    (g : X ⟶ (reindex i inverses).obj Y) :
    (Eᵤ).map ((leftHomEquiv i inverses X Y).symm g) =
      (PartialSliceLeftAdjunction.homEquiv i ((Eₜ).obj X) ((Eᵤ).obj Y)).symm ((Eₜ).map g) :=
  (Eᵤ).map_preimage _

theorem left_naturality_left {X X' : PartialMaps.Par (Over T)} {Y : PartialMaps.Par (Over U)}
    (f : X' ⟶ X) (g : X ⟶ (reindex i inverses).obj Y) :
    (leftHomEquiv i inverses X' Y).symm (f ≫ g) =
      (postcompose i).map f ≫ (leftHomEquiv i inverses X Y).symm g := by
  apply (Eᵤ).map_injective
  rw [leftHomEquiv_symm_value, (Eₜ).map_comp, (Eᵤ).map_comp,
    postcompose_value, leftHomEquiv_symm_value]
  exact PartialSliceLeftAdjunction.naturality_left i ((Eₜ).map f) ((Eₜ).map g)

theorem left_naturality_right {X : PartialMaps.Par (Over T)} {Y Y' : PartialMaps.Par (Over U)}
    (f : (postcompose i).obj X ⟶ Y) (g : Y ⟶ Y') :
    (leftHomEquiv i inverses X Y') (f ≫ g) =
      (leftHomEquiv i inverses X Y) f ≫ (reindex i inverses).map g := by
  apply (Eₜ).map_injective
  rw [leftHomEquiv_value, (Eᵤ).map_comp, (Eₜ).map_comp, leftHomEquiv_value, reindex_value]
  exact PartialSliceLeftAdjunction.naturality_right i (X := (Eₜ).obj X)
    ((Eᵤ).map f) ((Eᵤ).map g)

def leftAdjunction : postcompose i ⊣ reindex i inverses :=
  Adjunction.mkOfHomEquiv {
    homEquiv := leftHomEquiv i inverses
    homEquiv_naturality_left_symm := left_naturality_left i inverses
    homEquiv_naturality_right := left_naturality_right i inverses
  }

variable [Mono i]

def rightHomEquiv (Y : PartialMaps.Par (Over U)) (X : PartialMaps.Par (Over T)) :
    ((reindex i inverses).obj Y ⟶ X) ≃ (Y ⟶ (postcompose i).obj X) :=
  ((Functor.FullyFaithful.ofFullyFaithful Eₜ).homEquiv
    (X := (reindex i inverses).obj Y) (Y := X)).trans
    ((PartialSliceRightAdjunction.homEquiv i inverses ((Eᵤ).obj Y) ((Eₜ).obj X)).trans
      ((Functor.FullyFaithful.ofFullyFaithful Eᵤ).homEquiv
        (X := Y) (Y := (postcompose i).obj X)).symm)

theorem rightHomEquiv_value {Y : PartialMaps.Par (Over U)} {X : PartialMaps.Par (Over T)}
    (g : (reindex i inverses).obj Y ⟶ X) :
    (Eᵤ).map ((rightHomEquiv i inverses Y X) g) =
      (PartialSliceRightAdjunction.homEquiv i inverses ((Eᵤ).obj Y) ((Eₜ).obj X)) ((Eₜ).map g) :=
  (Eᵤ).map_preimage _

theorem rightHomEquiv_symm_value {Y : PartialMaps.Par (Over U)} {X : PartialMaps.Par (Over T)}
    (f : Y ⟶ (postcompose i).obj X) :
    (Eₜ).map ((rightHomEquiv i inverses Y X).symm f) =
      (PartialSliceRightAdjunction.homEquiv i inverses ((Eᵤ).obj Y) ((Eₜ).obj X)).symm
        ((Eᵤ).map f) :=
  (Eₜ).map_preimage _

theorem right_naturality_left {Y Y' : PartialMaps.Par (Over U)} {X : PartialMaps.Par (Over T)}
    (f : Y' ⟶ Y) (g : Y ⟶ (postcompose i).obj X) :
    (rightHomEquiv i inverses Y' X).symm (f ≫ g) =
      (reindex i inverses).map f ≫ (rightHomEquiv i inverses Y X).symm g := by
  apply (Eₜ).map_injective
  rw [rightHomEquiv_symm_value, (Eᵤ).map_comp, (Eₜ).map_comp,
    reindex_value, rightHomEquiv_symm_value]
  exact PartialSliceRightAdjunction.naturality_left i inverses (X := (Eₜ).obj X)
    ((Eᵤ).map f) ((Eᵤ).map g)

theorem right_naturality_right {Y : PartialMaps.Par (Over U)} {X X' : PartialMaps.Par (Over T)}
    (g : (reindex i inverses).obj Y ⟶ X) (h : X ⟶ X') :
    (rightHomEquiv i inverses Y X') (g ≫ h) =
      (rightHomEquiv i inverses Y X) g ≫ (postcompose i).map h := by
  apply (Eᵤ).map_injective
  rw [rightHomEquiv_value, (Eₜ).map_comp, (Eᵤ).map_comp, rightHomEquiv_value, postcompose_value]
  exact PartialSliceRightAdjunction.naturality_right i inverses ((Eₜ).map g) ((Eₜ).map h)

def rightAdjunction : reindex i inverses ⊣ postcompose i :=
  Adjunction.mkOfHomEquiv {
    homEquiv := rightHomEquiv i inverses
    homEquiv_naturality_left_symm := right_naturality_left i inverses
    homEquiv_naturality_right := right_naturality_right i inverses
  }

theorem right_unit_value (Y : PartialMaps.Par (Over U)) :
    (Eᵤ).map ((rightAdjunction i inverses).unit.app Y) =
      PartialSliceRightAdjunction.inverseFirst i inverses ((Eᵤ).obj Y) := by
  change (Eᵤ).map ((rightHomEquiv i inverses Y ((reindex i inverses).obj Y)) (𝟙 _)) = _
  rw [rightHomEquiv_value, (Eₜ).map_id]
  change PartialSliceRightAdjunction.inverseFirst i inverses ((Eᵤ).obj Y) ≫
    (PartialSlicePostcompose.functor i).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

end CategoricalEssentialIncompleteness.V46.PartialSliceChangeBase
