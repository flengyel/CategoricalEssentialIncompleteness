/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.LocalLifting
public import PCats.DomSemilattice

/-! # Comparison with the existing P-category formalization -/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms)
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness

section Coproducts

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]
variable [HasZeroMorphisms C] [CoprodStruct C] [CategoryTheory.HasCoproducts C]

/-- With zero morphisms, each categorical coproduct injection has a left inverse, and
hence is total. -/
instance (priority := 100) restrictionCoproductsOfZeros : RestrictionCoproducts C where
  total_i0 X Y := total_of_comp_total (i0 X Y) (copair (𝟙 X) (0 : Y ⟶ X))
    (by rw [i0_copair]; exact rst_id X)
  total_i1 X Y := total_of_comp_total (i1 X Y) (copair (0 : X ⟶ Y) (𝟙 Y))
    (by rw [i1_copair]; exact rst_id Y)

end Coproducts

section PCategories

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

/-- The two presentations have literally the same underlying endomorphisms,
restriction equations and order. -/
def idemOrderIso (X : C) : Idem X ≃o DomSemilattice X where
  toFun a := ⟨a.hom, a.restriction⟩
  invFun a := ⟨a.hom, a.isDomain⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

@[simp] theorem idemOrderIso_hom {X : C} (a : Idem X) : (idemOrderIso X a).hom = a.hom := rfl

theorem idemOrderIso_meet {X : C} (a b : Idem X) :
    idemOrderIso X (a ⊓ b) = DomSemilattice.meet (idemOrderIso X a) (idemOrderIso X b) := rfl

instance (priority := 100) rangesOfPCategory [HasRanges C] : Ranges C where
  range f := ⟨HasRanges.ran f, HasRanges.rst_ran f⟩
  receives := HasRanges.comp_ran
  agreement := HasRanges.ran_uniq

instance (priority := 100) zerosOfProdominical [HasZeroMorphisms C]
    [RecursionCategory.Prodominical C] : RestrictionZero C :=
  ⟨DomSemilattice.rst_zero⟩

theorem partialMono_iff_existing {X Y : C} (p : X ⟶ Y) :
    PartialMono p ↔ CategoryTheory.IsPartialMono p := Iff.rfl

theorem section_iff_existing {X Y : C} (p : X ⟶ Y) (s : Y ⟶ X) :
    SectionOf p s ↔ CategoryTheory.IsSection p s :=
  ⟨fun h => ⟨h.comp, h.receives⟩, fun h => ⟨h.comp_eq_rst, h.comp_self⟩⟩

instance (priority := 100) weakChoiceOfPCategory [CategoryTheory.HasWeakChoice C] :
    WeakChoice C where
  section_exists p hp := by
    obtain ⟨s, hs⟩ := CategoryTheory.HasWeakChoice.exists_isSection p hp
    exact ⟨s, (section_iff_existing p s).mpr hs⟩

end PCategories

section Split

variable {C : Type u} [Category.{v} C] [RestrictionCategory C] [RestrictionCategory.Split C]

instance (priority := 100) splitsOfExisting : Splits C where
  splitting a := by
    let m := RestrictionCategory.Split.incl (rst a.hom)
    let r := RestrictionCategory.Split.proj (rst a.hom)
    have hmr : m ≫ r = 𝟙 _ := RestrictionCategory.Split.proj_incl a.hom
    refine ⟨_, m, r, total_of_comp_total m r ?_, hmr, ?_⟩
    · rw [hmr]; exact rst_id _
    · exact (RestrictionCategory.Split.incl_proj a.hom).trans a.restriction

end Split

end CategoricalEssentialIncompleteness.LocalConnectedness
