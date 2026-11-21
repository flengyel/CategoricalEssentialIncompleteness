/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSliceSpanChangeBase
public import CategoricalEssentialIncompleteness.V46PartialSliceTheoryComparison

/-! # Sentence and theorem family comparisons on partial spans -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialSliceTheoryFamilies

open RestrictionSubobjects
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [HasPullbacks (Tot C)] (inverses : MonoInverses C) {T U : Tot C} (i : T ⟶ U)

def constantFunctor (P : Tot C) : C ⥤ PartialMaps.Par (Over P) :=
  ConstantFamilyProducts.constantFunctor P.obj ⋙ PartialSliceTuring.realization inverses P

theorem constant_value (P : Tot C) {X Y : C} (f : X ⟶ Y) :
    (PartialSliceEquivalence.functor inverses P).map ((constantFunctor inverses P).map f) =
      AmbientSliceTuring.constantMap P.obj f := PartialSliceTuring.map_realization inverses P _

theorem constant_total (P : Tot C) {X Y : C} (f : X ⟶ Y) (hf : isTotal f) :
    isTotal ((constantFunctor inverses P).map f) := by
  apply (PartialSliceEquivalence.total_iff inverses P _).mp
  rw [constant_value]
  exact (AmbientPartialSlice.total_iff _).mpr
    (PCategory.isTotal_nearProd_map (rst_id P.obj) hf)

def sentenceComparison (S : C) :
    (PartialSliceChangeBase.postcompose i).obj (PartialSliceTuring.constantObject T S) ⟶
      PartialSliceTuring.constantObject U S :=
  (PartialSliceEquivalence.functor inverses U).preimage
    (X := (PartialSliceChangeBase.postcompose i).obj (PartialSliceTuring.constantObject T S))
    (Y := PartialSliceTuring.constantObject U S) (PartialSliceTheoryComparison.baseComparison i S)

def comparison {X Y : C} (f : X ⟶ Y) :
    (PartialSliceChangeBase.postcompose i).obj (PartialSliceTuring.constantObject T X) ⟶
      PartialSliceTuring.constantObject U Y :=
  (PartialSliceEquivalence.functor inverses U).preimage
    (X := (PartialSliceChangeBase.postcompose i).obj (PartialSliceTuring.constantObject T X))
    (Y := PartialSliceTuring.constantObject U Y) (PartialSliceTheoryComparison.comparison i f)

theorem sentenceComparison_value (S : C) :
    (PartialSliceEquivalence.functor inverses U).map (sentenceComparison inverses i S) =
      PartialSliceTheoryComparison.baseComparison i S :=
  (PartialSliceEquivalence.functor inverses U).map_preimage _

theorem comparison_value {X Y : C} (f : X ⟶ Y) :
    (PartialSliceEquivalence.functor inverses U).map (comparison inverses i f) =
      PartialSliceTheoryComparison.comparison i f :=
  (PartialSliceEquivalence.functor inverses U).map_preimage _

theorem sentenceComparison_total (S : C) : isTotal (sentenceComparison inverses i S) := by
  apply (PartialSliceEquivalence.total_iff inverses U _).mp
  rw [sentenceComparison_value]
  exact PartialSliceTheoryComparison.baseComparison_total i S

theorem comparison_total {X Y : C} (f : X ⟶ Y) (hf : isTotal f) :
    isTotal (comparison inverses i f) := by
  apply (PartialSliceEquivalence.total_iff inverses U _).mp
  rw [comparison_value]
  apply (AmbientPartialSlice.total_iff _).mpr
  rw [PartialSliceTheoryComparison.comparison_value]
  exact PCategory.isTotal_nearProd_map i.property hf

theorem comparison_square {S : C} (t : T.obj ⟶ S) (u : U.obj ⟶ S) (ht : i.hom ≫ u = t) :
    (PartialSliceChangeBase.postcompose i).map ((constantFunctor inverses T).map t) ≫
        sentenceComparison inverses i S =
      comparison inverses i i.hom ≫ (constantFunctor inverses U).map u := by
  apply (PartialSliceEquivalence.functor inverses U).map_injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    PartialSliceChangeBase.postcompose_value, constant_value, sentenceComparison_value,
    comparison_value, constant_value]
  exact PartialSliceTheoryComparison.comparison_square i t u ht

variable [Mono i]

def sentenceIso (S : C) : PartialSliceTuring.constantObject T S ≅
    (PartialSliceChangeBase.reindex i inverses).obj (PartialSliceTuring.constantObject U S) :=
  (PartialSliceEquivalence.functor inverses T).preimageIso
    (X := PartialSliceTuring.constantObject T S)
    (Y := (PartialSliceChangeBase.reindex i inverses).obj (PartialSliceTuring.constantObject U S))
    (PartialSliceTheoryComparison.sentenceIso i inverses S)

theorem sentenceIso_hom_value (S : C) :
    (PartialSliceEquivalence.functor inverses T).map (sentenceIso inverses i S).hom =
      (PartialSliceTheoryComparison.sentenceIso i inverses S).hom :=
  (PartialSliceEquivalence.functor inverses T).map_preimage _

def theoremComparison : PartialSliceTuring.constantObject T T.obj ⟶
    (PartialSliceChangeBase.reindex i inverses).obj (PartialSliceTuring.constantObject U U.obj) :=
  (PartialSliceEquivalence.functor inverses T).preimage
    (X := PartialSliceTuring.constantObject T T.obj)
    (Y := (PartialSliceChangeBase.reindex i inverses).obj
      (PartialSliceTuring.constantObject U U.obj))
    (PartialSliceTheoryComparison.theoremComparison i)

omit [Mono i] in
theorem theoremComparison_value :
    (PartialSliceEquivalence.functor inverses T).map (theoremComparison inverses i) =
      PartialSliceTheoryComparison.theoremComparison i :=
  (PartialSliceEquivalence.functor inverses T).map_preimage _

theorem theorem_square {S : C} (t : T.obj ⟶ S) (u : U.obj ⟶ S) (ht : i.hom ≫ u = t) :
    (constantFunctor inverses T).map t ≫ (sentenceIso inverses i S).hom =
      theoremComparison inverses i ≫
        (PartialSliceChangeBase.reindex i inverses).map ((constantFunctor inverses U).map u) := by
  apply (PartialSliceEquivalence.functor inverses T).map_injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, constant_value,
    sentenceIso_hom_value, theoremComparison_value, PartialSliceChangeBase.reindex_value,
    constant_value]
  exact PartialSliceTheoryComparison.theorem_square i t u ht

omit [Mono i] in
theorem theoremComparison_total : isTotal (theoremComparison inverses i) := by
  apply (PartialSliceEquivalence.total_iff inverses T _).mp
  rw [theoremComparison_value]
  apply PartialSliceLeftAdjunction.lift_total
  apply (AmbientPartialSlice.total_iff _).mpr
  rw [PartialSliceTheoryComparison.comparison_value]
  exact PCategory.isTotal_nearProd_map i.property i.property

end CategoricalEssentialIncompleteness.V46.PartialSliceTheoryFamilies
