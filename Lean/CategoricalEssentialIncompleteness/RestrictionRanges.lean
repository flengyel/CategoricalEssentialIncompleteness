/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.RestrictionIdempotents
public import PCats.Coproducts

/-! # Ranges and binary restriction coproducts -/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (zero_comp comp_zero)
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]

/-- Ranges satisfy the agreement law. Their leastness follows from this law. -/
class Ranges (C : Type u) [Category.{v} C] [RestrictionCategory C] where
  range : {X Y : C} → (X ⟶ Y) → Idem Y
  receives : ∀ {X Y : C} (f : X ⟶ Y), f ≫ (range f).hom = f
  agreement : ∀ {X Y Z : C} (f : X ⟶ Y) (g h : Y ⟶ Z),
    f ≫ g = f ≫ h → (range f).hom ≫ g = (range f).hom ≫ h

namespace Ranges

variable [Ranges C]

theorem least {X Y : C} (f : X ⟶ Y) (a : Idem Y) (h : f ≫ a.hom = f) :
    range f ≤ a := by
  simpa only [Idem.le_def, Category.comp_id] using
    agreement f a.hom (𝟙 Y) (by rw [h, Category.comp_id])

theorem receives_of_le {X Y : C} (f : X ⟶ Y) (a : Idem Y)
    (h : range f ≤ a) : f ≫ a.hom = f := by
  calc
    _ = (f ≫ (range f).hom) ≫ a.hom := by rw [receives]
    _ = f := by rw [Category.assoc, show (range f).hom ≫ a.hom = (range f).hom from h,
      receives]

theorem of_idem {X : C} (a : Idem X) : range a.hom = a := by
  apply le_antisymm
  · exact least a.hom a a.idem
  · exact receives a.hom

theorem precomp_le {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    range (f ≫ g) ≤ range g :=
  least _ _ (by rw [Category.assoc, receives])

theorem precomp_split_epi {X Y Z : C} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) (g : Y ⟶ Z) : range (f ≫ g) = range g := by
  apply le_antisymm (precomp_le f g)
  have h := precomp_le s (f ≫ g)
  simpa only [← Category.assoc, hs, Category.id_comp] using h

end Ranges

/-- The injections of the chosen categorical coproducts are total. -/
class RestrictionCoproducts (C : Type u) [Category.{v} C] [RestrictionCategory C]
    [CoprodStruct C] [HasCoproducts C] : Prop where
  total_i0 : ∀ X Y : C, isTotal (i0 X Y)
  total_i1 : ∀ X Y : C, isTotal (i1 X Y)

section Coproducts

variable [CoprodStruct C] [HasCoproducts C]

theorem restrict_copair {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    rst (copair f g) = coprod_map (rst f) (rst g) := by
  apply hom_ext
  · rw [i0_coprod_map, ← rst_comp, i0_copair]
  · rw [i1_coprod_map, ← rst_comp, i1_copair]

variable [RestrictionCoproducts C]

theorem restrict_sum {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    rst (coprod_map f g) = coprod_map (rst f) (rst g) := by
  rw [coprod_map_eq_copair, restrict_copair,
    rst_comp_of_isTotal f (RestrictionCoproducts.total_i0 X Z),
    rst_comp_of_isTotal g (RestrictionCoproducts.total_i1 X Z)]

def Idem.sum {X Y : C} (a : Idem X) (b : Idem Y) : Idem (coprod X Y) :=
  ⟨coprod_map a.hom b.hom, by rw [restrict_sum, a.restriction, b.restriction]⟩

@[simp] theorem Idem.sum_hom {X Y : C} (a : Idem X) (b : Idem Y) :
    (a.sum b).hom = coprod_map a.hom b.hom := rfl

end Coproducts

section Joins

variable [Ranges C] [CoprodStruct C] [HasCoproducts C]

/-- Binary joins are the ranges of copairings. -/
instance (priority := 100) joinsOfRanges : BinaryJoins C where
  join a b := Ranges.range (copair a.hom b.hom)
  le_left a b := by
    change a.hom ≫ (Ranges.range (copair a.hom b.hom)).hom = a.hom
    have h := Ranges.receives (copair a.hom b.hom)
    have hi := congrArg (fun k => i0 _ _ ≫ k) h
    simpa only [← Category.assoc, i0_copair] using hi
  le_right a b := by
    change b.hom ≫ (Ranges.range (copair a.hom b.hom)).hom = b.hom
    have h := Ranges.receives (copair a.hom b.hom)
    have hi := congrArg (fun k => i1 _ _ ≫ k) h
    simpa only [← Category.assoc, i1_copair] using hi
  least a b c ha hb := Ranges.least _ c (by
    rw [copair_comp, show a.hom ≫ c.hom = a.hom from ha,
      show b.hom ≫ c.hom = b.hom from hb])

theorem sup_eq_range {X : C} (a b : Idem X) :
    a ⊔ b = Ranges.range (copair a.hom b.hom) := rfl

end Joins

section Summands

variable [CoprodStruct C] [HasCoproducts C] [RestrictionCoproducts C]
variable [Limits.HasZeroMorphisms C] [RestrictionZero C]

def summand0 (X Y : C) : Idem (coprod X Y) := (⊤ : Idem X).sum (⊥ : Idem Y)
def summand1 (X Y : C) : Idem (coprod X Y) := (⊥ : Idem X).sum (⊤ : Idem Y)

@[simp] theorem i0_summand0 (X Y : C) : i0 X Y ≫ (summand0 X Y).hom = i0 X Y := by
  simp only [summand0, Idem.sum_hom, Idem.top_hom, Idem.bot_hom, i0_coprod_map,
    Category.id_comp]

@[simp] theorem i1_summand0 (X Y : C) : i1 X Y ≫ (summand0 X Y).hom = 0 := by
  simp only [summand0, Idem.sum_hom, Idem.top_hom, Idem.bot_hom, i1_coprod_map, zero_comp]

@[simp] theorem i0_summand1 (X Y : C) : i0 X Y ≫ (summand1 X Y).hom = 0 := by
  simp only [summand1, Idem.sum_hom, Idem.top_hom, Idem.bot_hom, i0_coprod_map, zero_comp]

@[simp] theorem i1_summand1 (X Y : C) : i1 X Y ≫ (summand1 X Y).hom = i1 X Y := by
  simp only [summand1, Idem.sum_hom, Idem.top_hom, Idem.bot_hom, i1_coprod_map,
    Category.id_comp]

theorem summands_disjoint (X Y : C) : summand0 X Y ⊓ summand1 X Y = ⊥ := by
  apply Idem.ext
  apply hom_ext <;> simp only [Idem.inf_hom, ← Category.assoc, i0_summand0,
    i1_summand0, i0_summand1, zero_comp, Idem.bot_hom, comp_zero]

theorem summands_complementary [BinaryJoins C] (X Y : C) :
    Complementary (summand0 X Y) (summand1 X Y) := by
  refine ⟨summands_disjoint X Y, le_antisymm le_top ?_⟩
  change (𝟙 (coprod X Y)) ≫ (summand0 X Y ⊔ summand1 X Y).hom = 𝟙 _
  rw [Category.id_comp]
  apply hom_ext
  · have h := congrArg (fun k => i0 X Y ≫ k)
      (show (summand0 X Y).hom ≫ (summand0 X Y ⊔ summand1 X Y).hom =
        (summand0 X Y).hom from Idem.le_def.mp (le_sup_left :
          summand0 X Y ≤ summand0 X Y ⊔ summand1 X Y))
    simpa only [← Category.assoc, i0_summand0, Category.comp_id] using h
  · have h := congrArg (fun k => i1 X Y ≫ k)
      (show (summand1 X Y).hom ≫ (summand0 X Y ⊔ summand1 X Y).hom =
        (summand1 X Y).hom from Idem.le_def.mp (le_sup_right :
          summand1 X Y ≤ summand0 X Y ⊔ summand1 X Y))
    simpa only [← Category.assoc, i1_summand1, Category.comp_id] using h

end Summands

section Sections

/-- Partial monicity tests all partial arrows. -/
def PartialMono {X Y : C} (p : X ⟶ Y) : Prop :=
  ∀ {W : C} (u v : W ⟶ X), u ≫ p = v ≫ p → u ≫ rst p = v ≫ rst p

/-- The section equations in Section 2. -/
structure SectionOf {X Y : C} (p : X ⟶ Y) (s : Y ⟶ X) : Prop where
  comp : s ≫ p = rst s
  receives : p ≫ s ≫ p = p

/-- Weak choice asks for sections only of partial monomorphisms. -/
class WeakChoice (C : Type u) [Category.{v} C] [RestrictionCategory C] : Prop where
  section_exists : ∀ {X Y : C} (p : X ⟶ Y), PartialMono p → ∃ s, SectionOf p s

theorem SectionOf.domain [Ranges C] {X Y : C} {p : X ⟶ Y} {s : Y ⟶ X}
    (h : SectionOf p s) : Idem.ofRestrict s = Ranges.range p := by
  apply le_antisymm
  · change rst s ≫ (Ranges.range p).hom = rst s
    rw [← h.comp, Category.assoc, Ranges.receives]
  · exact Ranges.least _ _ (by change p ≫ rst s = p; rw [← h.comp, h.receives])

theorem SectionOf.support {X Y : C} {p : X ⟶ Y} {s : Y ⟶ X}
    (h : SectionOf p s) : s ≫ rst p = s := by
  rw [← rst_comp, h.comp, restrict_restrict, rst_comp_self]

theorem PartialMono.section_unique [Ranges C] {X Y : C} {p : X ⟶ Y}
    (hp : PartialMono p) {s t : Y ⟶ X} (hs : SectionOf p s) (ht : SectionOf p t) : s = t := by
  have hr : rst s = rst t := congrArg Idem.hom (hs.domain.trans ht.domain.symm)
  have hm := hp s t (by rw [hs.comp, ht.comp, hr])
  rwa [hs.support, ht.support] at hm

end Sections

end CategoricalEssentialIncompleteness.LocalConnectedness
