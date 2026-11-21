/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSliceEquivalence
public import CategoricalEssentialIncompleteness.V46AmbientSliceTuring

/-! # Universal computations in the monic partial-map slice -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialSliceTuring

open RestrictionSubobjects

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [HasPullbacks (Tot C)]
variable (inverses : MonoInverses C) (T : Tot C)

/-- The literal total family is an object of the monic partial-map slice. -/
def realizeObject (X : AmbientPartialSlice.Family T.obj) : PartialMaps.Par (Over T) :=
  ⟨Over.mk (⟨X.proj, X.total⟩ : (⟨X.base⟩ : Tot C) ⟶ T)⟩

def realization : AmbientPartialSlice.Family T.obj ⥤ PartialMaps.Par (Over T) where
  obj := realizeObject T
  map {X Y} f := (PartialSliceEquivalence.functor inverses T).preimage
    (X := realizeObject T X) (Y := realizeObject T Y) f
  map_id X := by
    apply (PartialSliceEquivalence.functor inverses T).map_injective
    rw [CategoryTheory.Functor.map_preimage, CategoryTheory.Functor.map_id]
    rfl
  map_comp f g := by
    apply (PartialSliceEquivalence.functor inverses T).map_injective
    rw [CategoryTheory.Functor.map_preimage, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_preimage, CategoryTheory.Functor.map_preimage]

theorem map_realization {X Y : AmbientPartialSlice.Family T.obj} (f : X ⟶ Y) :
    (PartialSliceEquivalence.functor inverses T).map ((realization inverses T).map f) = f :=
  (PartialSliceEquivalence.functor inverses T).map_preimage
    (X := realizeObject T X) (Y := realizeObject T Y) f

def constantObject (Q : C) : PartialMaps.Par (Over T) :=
  realizeObject T (AmbientSliceTuring.constantFamily T.obj Q)

/-- Product with the fixed input family, expressed in the span quotient. -/
def tensorFunctor (Q : C) : PartialMaps.Par (Over T) ⥤ PartialMaps.Par (Over T) :=
  PartialSliceEquivalence.functor inverses T ⋙ AmbientSliceTuring.tensorFunctor T.obj Q ⋙
    realization inverses T

def tensorFst (Q : C) (X : PartialMaps.Par (Over T)) :
    (tensorFunctor inverses T Q).obj X ⟶ X :=
  (PartialSliceEquivalence.functor inverses T).preimage
    (X := (tensorFunctor inverses T Q).obj X) (Y := X)
    (AmbientSliceTuring.tensorFst ((PartialSliceEquivalence.functor inverses T).obj X) Q)

def tensorSnd (Q : C) (X : PartialMaps.Par (Over T)) :
    (tensorFunctor inverses T Q).obj X ⟶ constantObject T Q :=
  (PartialSliceEquivalence.functor inverses T).preimage
    (X := (tensorFunctor inverses T Q).obj X) (Y := constantObject T Q)
    (AmbientSliceTuring.tensorSnd ((PartialSliceEquivalence.functor inverses T).obj X) Q)

theorem tensorFst_value (Q : C) (X : PartialMaps.Par (Over T)) :
    (PartialSliceEquivalence.functor inverses T).map (tensorFst inverses T Q X) =
      AmbientSliceTuring.tensorFst ((PartialSliceEquivalence.functor inverses T).obj X) Q :=
  (PartialSliceEquivalence.functor inverses T).map_preimage
    (X := (tensorFunctor inverses T Q).obj X) (Y := X) _

theorem tensorSnd_value (Q : C) (X : PartialMaps.Par (Over T)) :
    (PartialSliceEquivalence.functor inverses T).map (tensorSnd inverses T Q X) =
      AmbientSliceTuring.tensorSnd ((PartialSliceEquivalence.functor inverses T).obj X) Q :=
  (PartialSliceEquivalence.functor inverses T).map_preimage
    (X := (tensorFunctor inverses T Q).obj X) (Y := constantObject T Q) _

theorem tensorFst_total (Q : C) (X : PartialMaps.Par (Over T)) :
    isTotal (tensorFst inverses T Q X) := by
  apply (PartialSliceEquivalence.total_iff inverses T _).mp
  rw [tensorFst_value]
  exact AmbientSliceTuring.tensorFst_total _ _

theorem tensorSnd_total (Q : C) (X : PartialMaps.Par (Over T)) :
    isTotal (tensorSnd inverses T Q X) := by
  apply (PartialSliceEquivalence.total_iff inverses T _).mp
  rw [tensorSnd_value]
  exact AmbientSliceTuring.tensorSnd_total _ _

def tensorPair {Q : C} {V X : PartialMaps.Par (Over T)}
    (f : V ⟶ X) (g : V ⟶ constantObject T Q) :
    V ⟶ (tensorFunctor inverses T Q).obj X :=
  (PartialSliceEquivalence.functor inverses T).preimage
    (X := V) (Y := (tensorFunctor inverses T Q).obj X)
    (AmbientSliceTuring.tensorPair ((PartialSliceEquivalence.functor inverses T).map f)
      ((PartialSliceEquivalence.functor inverses T).map g))

theorem tensorPair_value {Q : C} {V X : PartialMaps.Par (Over T)}
    (f : V ⟶ X) (g : V ⟶ constantObject T Q) :
    (PartialSliceEquivalence.functor inverses T).map (tensorPair inverses T f g) =
      AmbientSliceTuring.tensorPair ((PartialSliceEquivalence.functor inverses T).map f)
        ((PartialSliceEquivalence.functor inverses T).map g) :=
  (PartialSliceEquivalence.functor inverses T).map_preimage
    (X := V) (Y := (tensorFunctor inverses T Q).obj X) _

theorem tensorPair_restriction {Q : C} {V X : PartialMaps.Par (Over T)}
    (f : V ⟶ X) (g : V ⟶ constantObject T Q) :
    rst (tensorPair inverses T f g) = rst f ≫ rst g := by
  apply (PartialSliceEquivalence.functor inverses T).map_injective
  rw [PartialSliceEquivalence.preserves_restrictions, tensorPair_value,
    AmbientSliceTuring.tensorPair_restriction, CategoryTheory.Functor.map_comp,
    PartialSliceEquivalence.preserves_restrictions,
    PartialSliceEquivalence.preserves_restrictions]

theorem tensorPair_fst {Q : C} {V X : PartialMaps.Par (Over T)}
    (f : V ⟶ X) (g : V ⟶ constantObject T Q) :
    tensorPair inverses T f g ≫ tensorFst inverses T Q X = rst g ≫ f := by
  apply (PartialSliceEquivalence.functor inverses T).map_injective
  rw [CategoryTheory.Functor.map_comp, tensorPair_value, tensorFst_value,
    AmbientSliceTuring.tensorPair_fst, CategoryTheory.Functor.map_comp,
    PartialSliceEquivalence.preserves_restrictions]

theorem tensorPair_snd {Q : C} {V X : PartialMaps.Par (Over T)}
    (f : V ⟶ X) (g : V ⟶ constantObject T Q) :
    tensorPair inverses T f g ≫ tensorSnd inverses T Q X = rst f ≫ g := by
  apply (PartialSliceEquivalence.functor inverses T).map_injective
  rw [CategoryTheory.Functor.map_comp, tensorPair_value, tensorSnd_value,
    AmbientSliceTuring.tensorPair_snd, CategoryTheory.Functor.map_comp,
    PartialSliceEquivalence.preserves_restrictions]

theorem tensorPair_proj {Q : C} {V X : PartialMaps.Par (Over T)}
    (h : V ⟶ (tensorFunctor inverses T Q).obj X) :
    tensorPair inverses T (h ≫ tensorFst inverses T Q X)
      (h ≫ tensorSnd inverses T Q X) = h := by
  apply (PartialSliceEquivalence.functor inverses T).map_injective
  rw [tensorPair_value, CategoryTheory.Functor.map_comp, tensorFst_value,
    CategoryTheory.Functor.map_comp, tensorSnd_value, AmbientSliceTuring.tensorPair_proj]

theorem tensorFunctor_restriction {Q : C} {X Y : PartialMaps.Par (Over T)} (f : X ⟶ Y) :
    (tensorFunctor inverses T Q).map (rst f) = rst ((tensorFunctor inverses T Q).map f) := by
  apply (PartialSliceEquivalence.functor inverses T).map_injective
  rw [PartialSliceEquivalence.preserves_restrictions]
  change (PartialSliceEquivalence.functor inverses T).map
      ((realization inverses T).map ((AmbientSliceTuring.tensorFunctor T.obj Q).map
        ((PartialSliceEquivalence.functor inverses T).map (rst f)))) =
    rst ((PartialSliceEquivalence.functor inverses T).map
      ((realization inverses T).map ((AmbientSliceTuring.tensorFunctor T.obj Q).map
        ((PartialSliceEquivalence.functor inverses T).map f))))
  rw [map_realization, map_realization, PartialSliceEquivalence.preserves_restrictions,
    AmbientSliceTuring.tensorFunctor_restriction]

/-- The chosen source is the product with the fixed input family on total morphisms, for
arbitrary objects of the partial-map slice. -/
theorem tensor_product_existsUnique {Q : C} {V X : PartialMaps.Par (Over T)}
    (f : V ⟶ X) (g : V ⟶ constantObject T Q) (hf : isTotal f) (hg : isTotal g) :
    ∃! h : V ⟶ (tensorFunctor inverses T Q).obj X, isTotal h ∧
      h ≫ tensorFst inverses T Q X = f ∧ h ≫ tensorSnd inverses T Q X = g := by
  let F := PartialSliceEquivalence.functor inverses T
  obtain ⟨h, ⟨ht, h0, h1⟩, hu⟩ := AmbientSliceTuring.tensor_product_existsUnique
    (F.map f) (F.map g) ((PartialSliceEquivalence.total_iff inverses T f).mpr hf)
      ((PartialSliceEquivalence.total_iff inverses T g).mpr hg)
  let h' : V ⟶ (tensorFunctor inverses T Q).obj X :=
    F.preimage (X := V) (Y := (tensorFunctor inverses T Q).obj X) h
  have hv : F.map h' = h := F.map_preimage
    (X := V) (Y := (tensorFunctor inverses T Q).obj X) h
  refine ⟨h', ⟨?_, ?_, ?_⟩, ?_⟩
  · apply (PartialSliceEquivalence.total_iff inverses T h').mp
    change isTotal (F.map h')
    rw [hv]
    exact ht
  · apply F.map_injective
    rw [F.map_comp, hv, tensorFst_value]
    exact h0
  · apply F.map_injective
    rw [F.map_comp, hv, tensorSnd_value]
    exact h1
  · rintro k ⟨hk, hk0, hk1⟩
    apply F.map_injective
    rw [hv]
    apply hu (F.map k)
    refine ⟨(PartialSliceEquivalence.total_iff inverses T k).mpr hk, ?_, ?_⟩
    · have he := congrArg F.map hk0
      rw [F.map_comp, tensorFst_value] at he
      exact he
    · have he := congrArg F.map hk1
      rw [F.map_comp, tensorSnd_value] at he
      exact he

def evaluator {Q : C} (τ : nearProd Q Q ⟶ Q) :
    (tensorFunctor inverses T Q).obj (constantObject T Q) ⟶ constantObject T Q :=
  (realization inverses T).map (AmbientSliceTuring.evaluator T.obj τ)

theorem evaluator_value {Q : C} (τ : nearProd Q Q ⟶ Q) :
    ((PartialSliceEquivalence.functor inverses T).map (evaluator inverses T τ)).hom =
      assoc T.obj Q Q ≫ nearProd_map (𝟙 T.obj) τ := by
  rw [evaluator, map_realization]
  rfl

/-- Every partial span with this source and target is computed by the slice evaluator
along a total parameter in the same partial-map slice. -/
theorem parameterization {Q : C} (τ : nearProd Q Q ⟶ Q)
    (hτ : RecursionCategory.IsTuringMorphism τ) (X : PartialMaps.Par (Over T))
    (φ : (tensorFunctor inverses T Q).obj X ⟶ constantObject T Q) :
    ∃ a : X ⟶ constantObject T Q, isTotal a ∧
      (tensorFunctor inverses T Q).map a ≫ evaluator inverses T τ = φ := by
  let F := PartialSliceEquivalence.functor inverses T
  obtain ⟨a, ha, hcode⟩ := AmbientSliceTuring.parameterization τ hτ (F.obj X) (F.map φ)
  let a' : X ⟶ constantObject T Q := F.preimage (X := X) (Y := constantObject T Q) a
  have hav : F.map a' = a := F.map_preimage (X := X) (Y := constantObject T Q) a
  have ha' : isTotal a' := by
    apply (PartialSliceEquivalence.total_iff inverses T a').mp
    change isTotal (F.map a')
    rw [hav]
    exact ha
  refine ⟨a', ha', ?_⟩
  apply F.map_injective
  rw [F.map_comp]
  change F.map ((realization inverses T).map
      ((AmbientSliceTuring.tensorFunctor T.obj Q).map (F.map a'))) ≫
    F.map ((realization inverses T).map (AmbientSliceTuring.evaluator T.obj τ)) = F.map φ
  rw [map_realization, map_realization]
  rw [hav]
  exact hcode

end CategoricalEssentialIncompleteness.V46.PartialSliceTuring
