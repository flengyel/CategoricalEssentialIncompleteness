/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalArithmeticCodedMaps
import CategoricalEssentialIncompleteness.V46NumericalUnderlying
import CategoricalEssentialIncompleteness.V46NumericalTuplesStructure
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! # A unary numerical image stores the output word alone -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.UnaryImage
local notation "U" => NumericalUnderlying.functor
variable {X : NumericalTuples.Object} {C : PredicateCategory 𝗧𝗔}

def object (f : X ⟶ NumericalCoordinates.predicateObject C) : NumericalTuples.Object :=
  NumericalCoordinates.predicateObject (CodedMaps.imagePredicate f)

theorem dimension (f : X ⟶ NumericalCoordinates.predicateObject C) : (object f).dimension = 1 := rfl

theorem membership (f : X ⟶ NumericalCoordinates.predicateObject C) (p : ℕ) :
    (object f).support p ↔ ∃ x : NumericalTuples.Point X, (f.toFun x).val = p :=
  CodedMaps.imagePredicate_eval f p

private theorem supported (f : X ⟶ NumericalCoordinates.predicateObject C)
    (p : NumericalTuples.Point (object f)) : C.val.Evalb (M := ℕ) ![p.val] := by
  obtain ⟨x,hx⟩ := (membership f p.val).mp p.property
  exact hx ▸ (f.toFun x).property

def inclusion (f : X ⟶ NumericalCoordinates.predicateObject C) :
    object f ⟶ NumericalCoordinates.predicateObject C where
  toFun p := ⟨p.val,supported f p⟩
  represented := ⟨Part.some,Partrec.some,fun _ => rfl⟩

theorem inclusion_value (f : X ⟶ NumericalCoordinates.predicateObject C)
    (p : NumericalTuples.Point (object f)) : ((inclusion f).toFun p).val = p.val := rfl

instance inclusion_mono (f : X ⟶ NumericalCoordinates.predicateObject C) : Mono (inclusion f) where
  right_cancellation g h he := by
    apply NumericalTuples.Map.ext
    funext z
    apply Subtype.ext
    exact congrArg (fun k => (k.toFun z).val) he

def quotient (f : X ⟶ NumericalCoordinates.predicateObject C) : X ⟶ object f where
  toFun x := ⟨(f.toFun x).val,(membership f _).mpr ⟨x,rfl⟩⟩
  represented := f.represented

theorem quotient_value (f : X ⟶ NumericalCoordinates.predicateObject C)
    (x : NumericalTuples.Point X) : ((quotient f).toFun x).val = (f.toFun x).val := rfl

theorem factor (f : X ⟶ NumericalCoordinates.predicateObject C) : quotient f ≫ inclusion f = f :=
  NumericalTuples.Map.ext rfl

theorem quotient_surjective (f : X ⟶ NumericalCoordinates.predicateObject C) :
    Function.Surjective (quotient f).toFun := by
  intro p
  obtain ⟨x,hx⟩ := (membership f p.val).mp p.property
  exact ⟨x,Subtype.ext hx⟩

private theorem splitEpi_of_surjective {A B : NumericalTuples.Object} (f : A ⟶ B)
    (hf : Function.Surjective f.toFun) : IsSplitEpi f := by
  have hs : EnumerableCarriers.Surjective (NumericalTuples.comparison.map f).hom := by
    intro n hn
    let y := (NumericalTuples.pointEquiv B).symm ⟨n,hn⟩
    obtain ⟨x,hx⟩ := hf y
    refine ⟨NumericalTuples.code A.dimension x.val,
      (NumericalTuples.comparisonMap_graph f _ n).mpr ⟨x,rfl,?_⟩⟩
    have hy : NumericalTuples.code B.dimension y.val = n :=
      NumericalTuples.pointEquiv_symm_code B ⟨n,hn⟩
    exact (congrArg (fun p : NumericalTuples.Point B => NumericalTuples.code B.dimension p.val) hx).trans hy
  let _ : IsSplitEpi (NumericalTuples.comparison.map f) :=
    EnumerableCarriers.isSplitEpi_of_surjective _ hs
  refine IsSplitEpi.mk' ⟨NumericalTuples.comparison.preimage
    (section_ (NumericalTuples.comparison.map f)),?_⟩
  apply NumericalTuples.comparison.map_injective
  simp

instance quotient_splitEpi (f : X ⟶ NumericalCoordinates.predicateObject C) : IsSplitEpi (quotient f) :=
  splitEpi_of_surjective (quotient f) (quotient_surjective f)

def imageFactorisation (f : X ⟶ NumericalCoordinates.predicateObject C) : StrongEpiMonoFactorisation f where
  I := object f
  m := inclusion f
  e := quotient f
  fac := factor f

def isImage (f : X ⟶ NumericalCoordinates.predicateObject C) :
    IsImage (imageFactorisation f).toMonoFactorisation :=
  (imageFactorisation f).toMonoIsImage

instance quotient_isIso (f : X ⟶ NumericalCoordinates.predicateObject C) [Mono f] : IsIso (quotient f) := by
  have hf : Function.Injective ((U).map f) := (mono_iff_injective _).mp inferInstance
  have hi : Function.Injective ((U).map (quotient f)) := by
    intro x y h
    apply hf
    apply Subtype.ext
    have hv := congrArg (fun p : NumericalTuples.Point (object f) => p.val) h
    change (f.toFun x).val = (f.toFun y).val
    exact hv
  let _ : IsIso ((U).map (quotient f)) :=
    (isIso_iff_bijective _).mpr ⟨hi,quotient_surjective f⟩
  exact isIso_of_reflects_iso (quotient f) (U)

def iso (f : X ⟶ NumericalCoordinates.predicateObject C) [Mono f] : X ≅ object f := asIso (quotient f)

theorem iso_inclusion (f : X ⟶ NumericalCoordinates.predicateObject C) [Mono f] :
    (iso f).hom ≫ inclusion f = f := factor f

theorem inverse_inclusion (f : X ⟶ NumericalCoordinates.predicateObject C) [Mono f] :
    (iso f).inv ≫ f = inclusion f := by
  calc
    _ = (iso f).inv ≫ ((iso f).hom ≫ inclusion f) :=
      congrArg (fun k => (iso f).inv ≫ k) (iso_inclusion f).symm
    _ = _ := Iso.inv_hom_id_assoc (iso f) (inclusion f)

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.UnaryImage
