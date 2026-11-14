/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46AmbientSliceProducts
public import CategoricalEssentialIncompleteness.V46RestrictionProductCategory
public import CategoricalEssentialIncompleteness.V46PartialSliceTuring

/-! # Binary restriction products in the actual monic partial-map slice -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialSliceProducts

open RestrictionSubobjects

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [HasPullbacks (Tot C)]
variable (inverses : MonoInverses C) (T : Tot C)

def product (X Y : PartialMaps.Par (Over T)) : PartialMaps.Par (Over T) :=
  PartialSliceTuring.realizeObject T (AmbientSliceProducts.product
    ((PartialSliceEquivalence.functor inverses T).obj X)
    ((PartialSliceEquivalence.functor inverses T).obj Y))

def first (X Y : PartialMaps.Par (Over T)) : product inverses T X Y ⟶ X :=
  (PartialSliceEquivalence.functor inverses T).preimage
    (X := product inverses T X Y) (Y := X) (AmbientSliceProducts.first
      ((PartialSliceEquivalence.functor inverses T).obj X)
      ((PartialSliceEquivalence.functor inverses T).obj Y))

def second (X Y : PartialMaps.Par (Over T)) : product inverses T X Y ⟶ Y :=
  (PartialSliceEquivalence.functor inverses T).preimage
    (X := product inverses T X Y) (Y := Y) (AmbientSliceProducts.second
      ((PartialSliceEquivalence.functor inverses T).obj X)
      ((PartialSliceEquivalence.functor inverses T).obj Y))

def pair {V X Y : PartialMaps.Par (Over T)} (f : V ⟶ X) (g : V ⟶ Y) :
    V ⟶ product inverses T X Y :=
  (PartialSliceEquivalence.functor inverses T).preimage
    (X := V) (Y := product inverses T X Y) (AmbientSliceProducts.pair
      ((PartialSliceEquivalence.functor inverses T).map f)
      ((PartialSliceEquivalence.functor inverses T).map g))

theorem first_value (X Y : PartialMaps.Par (Over T)) :
    (PartialSliceEquivalence.functor inverses T).map (first inverses T X Y) =
      AmbientSliceProducts.first ((PartialSliceEquivalence.functor inverses T).obj X)
        ((PartialSliceEquivalence.functor inverses T).obj Y) :=
  (PartialSliceEquivalence.functor inverses T).map_preimage
    (X := product inverses T X Y) (Y := X) _

theorem second_value (X Y : PartialMaps.Par (Over T)) :
    (PartialSliceEquivalence.functor inverses T).map (second inverses T X Y) =
      AmbientSliceProducts.second ((PartialSliceEquivalence.functor inverses T).obj X)
        ((PartialSliceEquivalence.functor inverses T).obj Y) :=
  (PartialSliceEquivalence.functor inverses T).map_preimage
    (X := product inverses T X Y) (Y := Y) _

theorem pair_value {V X Y : PartialMaps.Par (Over T)} (f : V ⟶ X) (g : V ⟶ Y) :
    (PartialSliceEquivalence.functor inverses T).map (pair inverses T f g) =
      AmbientSliceProducts.pair ((PartialSliceEquivalence.functor inverses T).map f)
        ((PartialSliceEquivalence.functor inverses T).map g) :=
  (PartialSliceEquivalence.functor inverses T).map_preimage
    (X := V) (Y := product inverses T X Y) _

theorem first_total (X Y : PartialMaps.Par (Over T)) : isTotal (first inverses T X Y) := by
  apply (PartialSliceEquivalence.total_iff inverses T _).mp
  rw [first_value]
  exact AmbientSliceProducts.first_total _ _

theorem second_total (X Y : PartialMaps.Par (Over T)) : isTotal (second inverses T X Y) := by
  apply (PartialSliceEquivalence.total_iff inverses T _).mp
  rw [second_value]
  exact AmbientSliceProducts.second_total _ _

theorem pair_fst {V X Y : PartialMaps.Par (Over T)} (f : V ⟶ X) (g : V ⟶ Y) :
    pair inverses T f g ≫ first inverses T X Y = rst g ≫ f := by
  apply (PartialSliceEquivalence.functor inverses T).map_injective
  rw [CategoryTheory.Functor.map_comp, pair_value, first_value,
    AmbientSliceProducts.pair_fst, CategoryTheory.Functor.map_comp,
    PartialSliceEquivalence.preserves_restrictions]

theorem pair_snd {V X Y : PartialMaps.Par (Over T)} (f : V ⟶ X) (g : V ⟶ Y) :
    pair inverses T f g ≫ second inverses T X Y = rst f ≫ g := by
  apply (PartialSliceEquivalence.functor inverses T).map_injective
  rw [CategoryTheory.Functor.map_comp, pair_value, second_value,
    AmbientSliceProducts.pair_snd, CategoryTheory.Functor.map_comp,
    PartialSliceEquivalence.preserves_restrictions]

theorem pair_restriction {V X Y : PartialMaps.Par (Over T)} (f : V ⟶ X) (g : V ⟶ Y) :
    rst (pair inverses T f g) = rst f ≫ rst g := by
  apply (PartialSliceEquivalence.functor inverses T).map_injective
  rw [PartialSliceEquivalence.preserves_restrictions, pair_value,
    AmbientSliceProducts.pair_restriction, CategoryTheory.Functor.map_comp,
    PartialSliceEquivalence.preserves_restrictions,
    PartialSliceEquivalence.preserves_restrictions]

theorem pair_proj {V X Y : PartialMaps.Par (Over T)} (h : V ⟶ product inverses T X Y) :
    pair inverses T (h ≫ first inverses T X Y) (h ≫ second inverses T X Y) = h := by
  apply (PartialSliceEquivalence.functor inverses T).map_injective
  rw [pair_value, CategoryTheory.Functor.map_comp, first_value,
    CategoryTheory.Functor.map_comp, second_value, AmbientSliceProducts.pair_proj]

def restrictionProducts : RestrictionProducts.ProductData (PartialMaps.Par (Over T)) where
  prod := product inverses T
  fst := first inverses T
  snd := second inverses T
  pair := pair inverses T
  fst_total := first_total inverses T
  snd_total := second_total inverses T
  pair_fst := pair_fst inverses T
  pair_snd := pair_snd inverses T
  pair_restriction := pair_restriction inverses T
  pair_proj := pair_proj inverses T

@[instance_reducible] def pcategoryStruct : PCategoryStruct (PartialMaps.Par (Over T)) :=
  (restrictionProducts inverses T).pcategoryStruct

theorem pcategoryLaws : @PCategory (PartialMaps.Par (Over T)) inferInstance
    (pcategoryStruct inverses T) := (restrictionProducts inverses T).pcategoryLaws

theorem restrictionCategory_eq :
    @PCategory.inducedRestriction (PartialMaps.Par (Over T)) inferInstance
      (pcategoryStruct inverses T) (pcategoryLaws inverses T) =
        (inferInstance : RestrictionCategory (PartialMaps.Par (Over T))) :=
  (restrictionProducts inverses T).restrictionCategory_eq

end CategoricalEssentialIncompleteness.V46.PartialSliceProducts
