/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSliceRightAdjunction
public import CategoricalEssentialIncompleteness.V46ConstantFamilyProducts

/-! # Sentence and theorem family comparisons under parameter inclusion -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialSliceTheoryComparison

open RestrictionSubobjects AmbientPartialSlice AmbientSliceTuring
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable {T U : Tot C} (i : T ⟶ U)

def baseComparison (S : C) :
    PartialSlicePostcompose.object i (constantFamily T.obj S) ⟶ constantFamily U.obj S :=
  ⟨nearProd_map i.hom (𝟙 S), by
    have ht : isTotal (nearProd_map i.hom (𝟙 S)) :=
      PCategory.isTotal_nearProd_map i.property (rst_id S)
    change nearProd_map i.hom (𝟙 S) ≫ p0 U.obj S =
      CategoryTheory.RestrictionCategory.rst (nearProd_map i.hom (𝟙 S)) ≫ (p0 T.obj S ≫ i.hom)
    rw [ht, Category.id_comp]
    exact PCategory.p0_nat i.hom⟩

theorem baseComparison_total (S : C) : isTotal (baseComparison i S) :=
  (AmbientPartialSlice.total_iff _).mpr (PCategory.isTotal_nearProd_map i.property (rst_id S))

def comparison {X Y : C} (f : X ⟶ Y) :
    PartialSlicePostcompose.object i (constantFamily T.obj X) ⟶ constantFamily U.obj Y :=
  baseComparison i X ≫ constantMap U.obj f

theorem comparison_value {X Y : C} (f : X ⟶ Y) :
    (comparison i f).hom = nearProd_map i.hom f := by
  change nearProd_map i.hom (𝟙 X) ≫ nearProd_map (𝟙 U.obj) f = _
  rw [PCategory.nearProd_comp, Category.comp_id, Category.id_comp]

theorem comparison_square {S : C} (t : T.obj ⟶ S) (u : U.obj ⟶ S)
    (ht : i.hom ≫ u = t) :
    (PartialSlicePostcompose.functor i).map (constantMap T.obj t) ≫ baseComparison i S =
      comparison i i.hom ≫ constantMap U.obj u := by
  apply Hom.ext
  change nearProd_map (𝟙 T.obj) t ≫ nearProd_map i.hom (𝟙 S) =
    (comparison i i.hom).hom ≫ nearProd_map (𝟙 U.obj) u
  rw [comparison_value, PCategory.nearProd_comp, PCategory.nearProd_comp]
  simp only [Category.id_comp, Category.comp_id, ht]

variable [Splits C] [HasPullbacks (Tot C)]

def sentenceForward (S : C) :
    constantFamily T.obj S ⟶ PartialSliceReindex.object i (constantFamily U.obj S) :=
  PartialSliceLeftAdjunction.lift i (baseComparison i S)

theorem forward_first (S : C) :
    (sentenceForward i S).hom ≫ (PartialSliceReindex.first i (constantFamily U.obj S)).hom =
      (baseComparison i S).hom := PartialSliceLeftAdjunction.lift_first i _

def sentenceBackward (S : C) :
    PartialSliceReindex.object i (constantFamily U.obj S) ⟶ constantFamily T.obj S :=
  ⟨partialPairing (PartialSliceReindex.object i (constantFamily U.obj S)).proj
      ((PartialSliceReindex.first i (constantFamily U.obj S)).hom ≫ p1 U.obj S), by
    let X := PartialSliceReindex.object i (constantFamily U.obj S)
    have hp : isTotal ((PartialSliceReindex.first i (constantFamily U.obj S)).hom ≫ p1 U.obj S) :=
      isTotal_comp ((AmbientPartialSlice.total_iff _).mp (PartialSliceReindex.first_total i _))
        (PCategory.p1_isTotal _ _)
    have ht := PCategory.isTotal_partialPairing X.total hp
    change partialPairing X.proj _ ≫ p0 T.obj S =
      PCategoryStruct.rst (partialPairing X.proj _) ≫ X.proj
    rw [PCategory.p0_partialPairing_of_isTotal _ hp, ht, Category.id_comp]⟩

omit [Splits C] in
theorem backward_first (S : C) :
    (sentenceBackward i S).hom ≫ (baseComparison i S).hom =
      (PartialSliceReindex.first i (constantFamily U.obj S)).hom := by
  let X := PartialSliceReindex.object i (constantFamily U.obj S)
  let p : X.base ⟶ nearProd U.obj S := (PartialSliceReindex.first i (constantFamily U.obj S)).hom
  have hp : isTotal p :=
    (AmbientPartialSlice.total_iff _).mp
      (PartialSliceReindex.first_total i (constantFamily U.obj S))
  have h0 : p ≫ p0 U.obj S = X.proj ≫ i.hom := by
    have h := (PartialSliceReindex.first i (constantFamily U.obj S)).over
    change p ≫ p0 U.obj S = CategoryTheory.RestrictionCategory.rst p ≫ (X.proj ≫ i.hom) at h
    rw [hp, Category.id_comp] at h
    exact h
  change partialPairing X.proj (p ≫ p1 U.obj S) ≫ nearProd_map i.hom (𝟙 S) = p
  rw [PCategory.partialPairing_comp_nearProd_map, Category.comp_id, ← h0,
    PCategory.partialPairing_proj]

theorem backward_forward (S : C) : sentenceBackward i S ≫ sentenceForward i S = 𝟙 _ := by
  apply PartialSliceReindex.hom_ext i
  change ((sentenceBackward i S).hom ≫ (sentenceForward i S).hom) ≫
      (PartialSliceReindex.first i (constantFamily U.obj S)).hom = 𝟙 _ ≫ _
  rw [Category.assoc, forward_first i S, backward_first i S]
  exact (Category.id_comp _).symm

variable (inverses : MonoInverses C) [Mono i]

include inverses in
theorem forward_backward (S : C) : sentenceForward i S ≫ sentenceBackward i S = 𝟙 _ := by
  have hs : (baseComparison i S).hom ≫ nearProd_map (inverse inverses i) (𝟙 S) =
      𝟙 (nearProd T.obj S) := by
    change nearProd_map i.hom (𝟙 S) ≫ nearProd_map (inverse inverses i) (𝟙 S) = _
    rw [PCategory.nearProd_comp, hom_inverse, Category.id_comp, PCategory.nearProd_id]
  have h : ((sentenceForward i S).hom ≫ (sentenceBackward i S).hom) ≫
      (baseComparison i S).hom = (baseComparison i S).hom := by
    rw [Category.assoc, backward_first i S]
    exact forward_first i S
  have hh := congrArg (fun k => k ≫ nearProd_map (inverse inverses i) (𝟙 S)) h
  apply Hom.ext
  change (sentenceForward i S).hom ≫ (sentenceBackward i S).hom = 𝟙 (nearProd T.obj S)
  have hh' : ((sentenceForward i S).hom ≫ (sentenceBackward i S).hom) ≫
      𝟙 (nearProd T.obj S) = 𝟙 (nearProd T.obj S) := by
    simpa only [Category.assoc, hs] using hh
  exact (Category.comp_id ((sentenceForward i S).hom ≫ (sentenceBackward i S).hom)).symm.trans hh'

def sentenceIso (S : C) :
    constantFamily T.obj S ≅ PartialSliceReindex.object i (constantFamily U.obj S) where
  hom := sentenceForward i S
  inv := sentenceBackward i S
  hom_inv_id := forward_backward i inverses S
  inv_hom_id := backward_forward i S

omit inverses [Mono i] in
def theoremComparison : constantFamily T.obj T.obj ⟶
    PartialSliceReindex.object i (constantFamily U.obj U.obj) :=
  PartialSliceLeftAdjunction.lift i (comparison i i.hom)

omit inverses [Mono i] in
theorem theorem_square {S : C} (t : T.obj ⟶ S) (u : U.obj ⟶ S) (ht : i.hom ≫ u = t) :
    constantMap T.obj t ≫ sentenceForward i S =
      theoremComparison i ≫ (PartialSliceReindex.functor i).map (constantMap U.obj u) := by
  calc
    _ = PartialSliceLeftAdjunction.lift i
        ((PartialSlicePostcompose.functor i).map (constantMap T.obj t) ≫ baseComparison i S) :=
      (PartialSliceLeftAdjunction.lift_naturality_left i _ _).symm
    _ = PartialSliceLeftAdjunction.lift i (comparison i i.hom ≫ constantMap U.obj u) :=
      congrArg (PartialSliceLeftAdjunction.lift i) (comparison_square i t u ht)
    _ = _ := PartialSliceLeftAdjunction.lift_naturality_right i _ _

end CategoricalEssentialIncompleteness.V46.PartialSliceTheoryComparison
