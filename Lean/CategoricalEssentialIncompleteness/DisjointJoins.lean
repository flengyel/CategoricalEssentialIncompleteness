/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.LocalLifting

/-! # Disjoint arrow joins supply section lifts -/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms zero_comp comp_zero)
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness

variable {C : Type u₁} [Category.{v₁} C] [RestrictionCategory C]

/-- The restriction order on parallel partial arrows. -/
def ArrowLE {X Y : C} (f g : X ⟶ Y) : Prop := rst f ≫ g = f

theorem ArrowLE.domain {X Y : C} {f g : X ⟶ Y} (h : ArrowLE f g) :
    Idem.ofRestrict f ≤ Idem.ofRestrict g := by
  change rst f ≫ rst g = rst f
  rw [← rst_comp_rst, show rst f ≫ g = f from h]

/-- Least upper bounds of arrows whose restrictions are disjoint. -/
class DisjointArrowJoins (C : Type u₁) [Category.{v₁} C] [RestrictionCategory C]
    [HasZeroMorphisms C] [RestrictionZero C] : Prop where
  exists_join : ∀ {X Y : C} (f g : X ⟶ Y),
    Idem.ofRestrict f ⊓ Idem.ofRestrict g = ⊥ →
    ∃ ℓ : X ⟶ Y, ArrowLE f ℓ ∧ ArrowLE g ℓ ∧
      ∀ h : X ⟶ Y, ArrowLE f h → ArrowLE g h → ArrowLE ℓ h

variable [HasZeroMorphisms C] [RestrictionZero C]
variable [CoprodStruct C] [CategoryTheory.HasCoproducts C] [RestrictionCoproducts C]

/-- Proposition 6.4, the construction of the total switch as a disjoint
join in the restriction order. -/
theorem disjoint_joins_switch [DisjointArrowJoins C] {X : C}
    (c c' : Idem X) (hc : PairComplementary c c') :
    ∃ ℓ : X ⟶ coprod X X, isTotal ℓ ∧
      c.hom ≫ ℓ = c.hom ≫ i1 X X ∧ c'.hom ≫ ℓ = c'.hom ≫ i0 X X ∧
      ∀ h : X ⟶ coprod X X,
        ArrowLE (c.hom ≫ i1 X X) h → ArrowLE (c'.hom ≫ i0 X X) h → ArrowLE ℓ h := by
  have h1 : Idem.ofRestrict (c.hom ≫ i1 X X) = c := by
    apply Idem.ext
    exact (rst_comp_of_isTotal _ (RestrictionCoproducts.total_i1 X X)).trans c.restriction
  have h0 : Idem.ofRestrict (c'.hom ≫ i0 X X) = c' := by
    apply Idem.ext
    exact (rst_comp_of_isTotal _ (RestrictionCoproducts.total_i0 X X)).trans c'.restriction
  obtain ⟨ℓ, hl1, hl0, hleast⟩ := DisjointArrowJoins.exists_join
    (c.hom ≫ i1 X X) (c'.hom ≫ i0 X X) (by rw [h1, h0, hc.disjoint])
  have hle1 := hl1.domain
  have hle0 := hl0.domain
  rw [h1] at hle1
  rw [h0] at hle0
  have ht : Idem.ofRestrict ℓ = ⊤ :=
    le_antisymm le_top (hc.cover _ hle1 hle0)
  have he1 : c.hom ≫ ℓ = c.hom ≫ i1 X X := by
    have hh := congrArg Idem.hom h1
    change rst (c.hom ≫ i1 X X) = c.hom at hh
    change rst (c.hom ≫ i1 X X) ≫ ℓ = c.hom ≫ i1 X X at hl1
    rwa [hh] at hl1
  have he0 : c'.hom ≫ ℓ = c'.hom ≫ i0 X X := by
    have hh := congrArg Idem.hom h0
    change rst (c'.hom ≫ i0 X X) = c'.hom at hh
    change rst (c'.hom ≫ i0 X X) ≫ ℓ = c'.hom ≫ i0 X X at hl0
    rwa [hh] at hl0
  exact ⟨ℓ, congrArg Idem.hom ht, he1, he0, hleast⟩

variable [BinaryJoins C]
variable {A : Type u₂} [Category.{v₂} A] [RestrictionCategory A]
variable [HasZeroMorphisms A] [RestrictionZero A] [BinaryJoins A]
variable [CoprodStruct A] [CategoryTheory.HasCoproducts A] [RestrictionCoproducts A]
variable [Ranges C] [Ranges A] [Splits A] [JoinInverse A] [LocallyConnected A] [WeakChoice A]

omit [RestrictionCoproducts C] in
/-- The two restriction equations alone identify the image with the unique
target section. -/
theorem image_switch_eq (F : RangeFunctor C A) {X : C}
    (c c' : Idem X) (hc : Complementary c c') (ℓ : X ⟶ coprod X X)
    (h1 : c.hom ≫ ℓ = c.hom ≫ i1 X X)
    (h0 : c'.hom ≫ ℓ = c'.hom ≫ i0 X X) :
    F.toFunctor.map ℓ =
      switchSection (F.mapIdem c) (F.mapIdem c') (F.map_complementary hc) ≫
        (F.comparison X X).hom := by
  let s := switchSection (F.mapIdem c) (F.mapIdem c') (F.map_complementary hc)
  have hs := switchSection_spec (F.mapIdem c) (F.mapIdem c') (F.map_complementary hc)
  have he : F.toFunctor.map ℓ ≫ (F.comparison X X).inv = s := by
    apply complementary_hom_ext (F.map_complementary hc)
    · change F.toFunctor.map c.hom ≫ (F.toFunctor.map ℓ ≫ _) = _
      rw [← Category.assoc, ← F.toFunctor.map_comp, h1, F.toFunctor.map_comp,
        Category.assoc, ← F.i1_comparison, Category.assoc, Iso.hom_inv_id,
        Category.comp_id, hs.2.2.1]
      rfl
    · change F.toFunctor.map c'.hom ≫ (F.toFunctor.map ℓ ≫ _) = _
      rw [← Category.assoc, ← F.toFunctor.map_comp, h0, F.toFunctor.map_comp,
        Category.assoc, ← F.i0_comparison, Category.assoc, Iso.hom_inv_id,
        Category.comp_id, hs.2.2.2]
      rfl
  have hh := congrArg (fun k => k ≫ (F.comparison X X).hom) he
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hh

/-- Proposition 6.4, its range-functor conclusion. -/
theorem disjoint_joins_lift [DisjointArrowJoins C] (F : RangeFunctor C A)
    {X : C} (c c' : Idem X) (hc : Complementary c c') :
    ∃ ℓ : X ⟶ coprod X X, isTotal ℓ ∧
      F.toFunctor.map ℓ =
        switchSection (F.mapIdem c) (F.mapIdem c') (F.map_complementary hc) ≫
          (F.comparison X X).hom := by
  obtain ⟨ℓ, ht, h1, h0, _⟩ := disjoint_joins_switch c c' hc.toPair
  exact ⟨ℓ, ht, image_switch_eq F c c' hc ℓ h1 h0⟩

end CategoricalEssentialIncompleteness.LocalConnectedness
