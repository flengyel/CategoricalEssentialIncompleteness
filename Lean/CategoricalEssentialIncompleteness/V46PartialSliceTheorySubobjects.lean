/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSliceTheoryFamilies
public import Mathlib.CategoryTheory.Subobject.Basic

/-! # The theorem-family subobject bound in the actual total slice -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v v' u u'
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialSliceTheoryFamilies

open RestrictionSubobjects

theorem mono_of_retraction {D : Type u'} [Category.{v'} D] {A B : D}
    (m : A ⟶ B) (r : B ⟶ A) (h : m ≫ r = 𝟙 A) : Mono m := by
  constructor
  intro Z f g he
  have hh := congrArg (fun k => k ≫ r) he
  simpa only [Category.assoc, h, Category.comp_id] using hh

theorem total_mono {D : Type u'} [Category.{v'} D] [RestrictionCategory D]
    {A B : Tot D} (m : A ⟶ B) (hm : Mono m.hom) : Mono m := by
  let : Mono m.hom := hm
  constructor
  intro Z f g he
  apply WideSubcategory.hom_ext
  apply (cancel_mono m.hom).mp
  exact congrArg (fun k => k.hom) he

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [HasPullbacks (Tot C)] (inverses : MonoInverses C)

theorem constant_section (P : Tot C) {A B : Tot C} (m : A ⟶ B) [Mono m] :
    (constantFunctor inverses P).map m.hom ≫
      (constantFunctor inverses P).map (inverse inverses m) =
        𝟙 ((constantFunctor inverses P).obj A.obj) := by
  rw [← CategoryTheory.Functor.map_comp, hom_inverse, CategoryTheory.Functor.map_id]

theorem constant_mono (P : Tot C) {A B : Tot C} (m : A ⟶ B) [Mono m] :
    Mono ((constantFunctor inverses P).map m.hom) :=
  mono_of_retraction _ _ (constant_section inverses P m)

abbrev TotalSlice (P : Tot C) := Tot (PartialMaps.Par (Over P))

def constantTotal (P : Tot C) (X : C) : TotalSlice P := ⟨PartialSliceTuring.constantObject P X⟩

def sourceTheory {T S : Tot C} (t : T ⟶ S) :
    constantTotal T T.obj ⟶ constantTotal T S.obj :=
  ⟨(constantFunctor inverses T).map t.hom, constant_total inverses T t.hom t.property⟩

def sourceTheorySubobject {T S : Tot C} (t : T ⟶ S) [Mono t] :
    Subobject (constantTotal T S.obj) := by
  let := total_mono (sourceTheory inverses t) (constant_mono inverses T t)
  exact Subobject.mk (sourceTheory inverses t)

variable {T U S : Tot C} (i : T ⟶ U) [Mono i]

def pulledTheory (u : U ⟶ S) :
    (⟨(PartialSliceChangeBase.reindex i inverses).obj
      (PartialSliceTuring.constantObject U U.obj)⟩ : TotalSlice T) ⟶ constantTotal T S.obj :=
  ⟨(PartialSliceChangeBase.reindex i inverses).map ((constantFunctor inverses U).map u.hom) ≫
      (sentenceIso inverses i S.obj).inv,
    isTotal_comp (PreservesRestriction.total
      (PartialSliceChangeBase.reindex_restriction i inverses) _
      (constant_total inverses U u.hom u.property)) (iso_total (sentenceIso inverses i S.obj).symm)⟩

def pulledTheoryRetraction (u : U ⟶ S) [Mono u] :
    PartialSliceTuring.constantObject T S.obj ⟶
      (PartialSliceChangeBase.reindex i inverses).obj (PartialSliceTuring.constantObject U U.obj) :=
  (sentenceIso inverses i S.obj).hom ≫
    (PartialSliceChangeBase.reindex i inverses).map
      ((constantFunctor inverses U).map (inverse inverses u))

theorem pulledTheory_section (u : U ⟶ S) [Mono u] :
    (pulledTheory inverses i u).hom ≫ pulledTheoryRetraction inverses i u = 𝟙 _ := by
  change ((PartialSliceChangeBase.reindex i inverses).map
        ((constantFunctor inverses U).map u.hom) ≫ (sentenceIso inverses i S.obj).inv) ≫
      ((sentenceIso inverses i S.obj).hom ≫
        (PartialSliceChangeBase.reindex i inverses).map
          ((constantFunctor inverses U).map (inverse inverses u))) = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← CategoryTheory.Functor.map_comp, constant_section, CategoryTheory.Functor.map_id]
  rfl

def pulledTheorySubobject (u : U ⟶ S) [Mono u] : Subobject (constantTotal T S.obj) := by
  let hm := mono_of_retraction _ _ (pulledTheory_section inverses i u)
  let := total_mono (pulledTheory inverses i u) hm
  exact Subobject.mk (pulledTheory inverses i u)

/-- The printed theory family is below the pulled-back theory family after
the sentence-family isomorphism, as subobjects of the actual total slice. -/
theorem theory_bound (t : T ⟶ S) (u : U ⟶ S) [Mono t] [Mono u] (ht : i ≫ u = t) :
    sourceTheorySubobject inverses t ≤ pulledTheorySubobject inverses i u := by
  let := total_mono (sourceTheory inverses t) (constant_mono inverses T t)
  let hm := mono_of_retraction _ _ (pulledTheory_section inverses i u)
  let := total_mono (pulledTheory inverses i u) hm
  change Subobject.mk (sourceTheory inverses t) ≤ Subobject.mk (pulledTheory inverses i u)
  let w : constantTotal T T.obj ⟶ (⟨(PartialSliceChangeBase.reindex i inverses).obj
      (PartialSliceTuring.constantObject U U.obj)⟩ : TotalSlice T) :=
    ⟨theoremComparison inverses i, theoremComparison_total inverses i⟩
  apply Subobject.mk_le_mk_of_comm w
  apply WideSubcategory.hom_ext
  change theoremComparison inverses i ≫
      ((PartialSliceChangeBase.reindex i inverses).map ((constantFunctor inverses U).map u.hom) ≫
        (sentenceIso inverses i S.obj).inv) = (constantFunctor inverses T).map t.hom
  have ht' : i.hom ≫ u.hom = t.hom := congrArg (fun k => k.hom) ht
  rw [← Category.assoc, ← theorem_square inverses i t.hom u.hom ht', Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end CategoricalEssentialIncompleteness.V46.PartialSliceTheoryFamilies
