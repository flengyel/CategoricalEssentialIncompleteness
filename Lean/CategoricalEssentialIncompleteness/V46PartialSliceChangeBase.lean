/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSliceRightAdjunction
public import CategoricalEssentialIncompleteness.V46PartialSliceProperness
public import CategoricalEssentialIncompleteness.V46PartialSliceRealization

/-! # Postcomposition and reindexing in the actual monic-span quotient -/

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
variable [HasPullbacks (Tot C)] {T U V : Tot C} (i : T ⟶ U)

local instance overMapMonos : (Over.map i).PreservesMonomorphisms where
  preserves f _ := by
    have : Mono f.left := Over.mono_left_of_mono f
    have : Mono ((Over.map i).map f).left := by
      change Mono f.left
      infer_instance
    exact Over.mono_of_mono_left _

local instance overMapPullbacks : PreservesLimitsOfShape WalkingCospan (Over.map i) := by
  let : PreservesLimitsOfShape WalkingCospan (Over.map i ⋙ Over.forget U) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (Over.forget T))
  exact preservesLimitsOfShape_of_reflects_of_preserves (Over.map i) (Over.forget U)

def postcompose : PartialMaps.Par (Over T) ⥤ PartialMaps.Par (Over U) :=
  PartialMaps.inducedFunctor (Over.map i)

omit [Splits C] in
theorem postcompose_object (X : PartialMaps.Par (Over T)) :
    PartialSliceEquivalence.objectMap U ((postcompose i).obj X) =
      PartialSlicePostcompose.object i (PartialSliceEquivalence.objectMap T X) := rfl

variable (inverses : MonoInverses C)

theorem postcompose_value {X Y : PartialMaps.Par (Over T)} (f : X ⟶ Y) :
    (PartialSliceEquivalence.functor inverses U).map ((postcompose i).map f) =
      (PartialSlicePostcompose.functor i).map
        ((PartialSliceEquivalence.functor inverses T).map f) := by
  apply AmbientPartialSlice.Hom.ext
  induction f using Quotient.inductionOn with | _ s => rfl

def reindex : PartialMaps.Par (Over U) ⥤ PartialMaps.Par (Over T) :=
  PartialSliceEquivalence.functor inverses U ⋙ PartialSliceReindex.functor i ⋙
    PartialSliceTuring.realization inverses T

theorem reindex_object_left (Y : PartialMaps.Par (Over U)) :
    ((reindex i inverses).obj Y).obj.left = pullback Y.obj.hom i := rfl

theorem reindex_object_hom (Y : PartialMaps.Par (Over U)) :
    ((reindex i inverses).obj Y).obj.hom = pullback.snd Y.obj.hom i := rfl

theorem reindex_value {X Y : PartialMaps.Par (Over U)} (f : X ⟶ Y) :
    (PartialSliceEquivalence.functor inverses T).map ((reindex i inverses).map f) =
      (PartialSliceReindex.functor i).map ((PartialSliceEquivalence.functor inverses U).map f) :=
  PartialSliceTuring.map_realization inverses T _

include inverses in
theorem postcompose_faithful : (postcompose i).Faithful where
  map_injective {X Y} f g h := by
    apply (PartialSliceEquivalence.functor inverses T).map_injective
    apply (PartialSlicePostcompose.functor i).map_injective
    rw [← postcompose_value i inverses f, ← postcompose_value i inverses g, h]

omit inverses [Splits C] in
theorem postcompose_restriction : PreservesRestriction (postcompose i) :=
  PartialMaps.inducedFunctor_restriction (Over.map i)

theorem reindex_restriction : PreservesRestriction (reindex i inverses) := by
  intro X Y f
  apply (PartialSliceEquivalence.functor inverses T).map_injective
  rw [reindex_value, PartialSliceEquivalence.preserves_restrictions,
    PartialSliceReindex.preserves_restriction, PartialSliceEquivalence.preserves_restrictions,
    reindex_value]

variable [Mono i]

include inverses in
theorem postcompose_full : (postcompose i).Full where
  map_surjective {X Y} f := by
    let := PartialSlicePostcompose.full i inverses
    let g : X ⟶ Y := (PartialSliceEquivalence.functor inverses T).preimage
      (X := X) (Y := Y) ((PartialSlicePostcompose.functor i).preimage
        (X := (PartialSliceEquivalence.functor inverses T).obj X)
        (Y := (PartialSliceEquivalence.functor inverses T).obj Y)
        ((PartialSliceEquivalence.functor inverses U).map f))
    refine ⟨g, ?_⟩
    apply (PartialSliceEquivalence.functor inverses U).map_injective
    rw [postcompose_value]
    change (PartialSlicePostcompose.functor i).map
      ((PartialSliceEquivalence.functor inverses T).map g) = _
    rw [CategoryTheory.Functor.map_preimage, CategoryTheory.Functor.map_preimage]

include inverses in
theorem not_essSurj (proper : ¬ IsIso i) : ¬ (postcompose i).EssSurj := by
  intro h
  let : (postcompose i).EssSurj := h
  let Z : PartialMaps.Par (Over U) :=
    ⟨Over.mk (𝟙 U)⟩
  let X := (postcompose i).objPreimage Z
  let j := (postcompose i).objObjPreimageIso Z
  have hX : IsIso i := by
    exact PartialSliceProperness.isIso_of_terminal_image i
      (PartialSliceEquivalence.objectMap T X)
      ((PartialSliceEquivalence.functor inverses U).mapIso j)
  exact proper hX

end CategoricalEssentialIncompleteness.V46.PartialSliceChangeBase
