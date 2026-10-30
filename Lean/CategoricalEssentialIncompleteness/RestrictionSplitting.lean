/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.RestrictionRanges

/-! # The restriction splitting and preservation of inseparability -/

universe v u

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms zero_comp comp_zero)

namespace CategoricalEssentialIncompleteness.LocalConnectedness

variable (C : Type u) [Category.{v} C] [RestrictionCategory C]

/-- Objects of the restriction splitting. -/
structure SplitObject where
  base : C
  domain : Idem base

namespace SplitObject

variable {C}

/-- The two support equations are equivalent to `f = d ≫ f ≫ e` in the
manuscript's composition convention. -/
@[ext] structure Hom (X Y : SplitObject C) where
  hom : X.base ⟶ Y.base
  source : X.domain.hom ≫ hom = hom
  target : hom ≫ Y.domain.hom = hom

instance : Category.{v} (SplitObject C) where
  Hom := Hom
  id X := ⟨X.domain.hom, X.domain.idem, X.domain.idem⟩
  comp f g := ⟨f.hom ≫ g.hom, by rw [← Category.assoc, f.source],
    by rw [Category.assoc, g.target]⟩
  id_comp f := Hom.ext f.source
  comp_id f := Hom.ext f.target
  assoc f g h := Hom.ext (Category.assoc f.hom g.hom h.hom)

@[simp] theorem id_hom (X : SplitObject C) : (𝟙 X : X ⟶ X).hom = X.domain.hom := rfl
@[simp] theorem comp_hom {X Y Z : SplitObject C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

theorem restriction_source {X Y : SplitObject C} (f : X ⟶ Y) :
    X.domain.hom ≫ rst f.hom = rst f.hom := by
  calc
    _ = rst (X.domain.hom ≫ f.hom) := by
      rw [← X.domain.restriction, rst_comp_rst]
    _ = _ := by rw [f.source]

def restriction {X Y : SplitObject C} (f : X ⟶ Y) : X ⟶ X :=
  ⟨rst f.hom, restriction_source f, by
    have h := rst_comm f.hom X.domain.hom
    rw [X.domain.restriction] at h
    exact h.trans (restriction_source f)⟩

instance : RestrictionCategory (SplitObject C) where
  rst := restriction
  rst_comp_self f := Hom.ext (rst_comp_self f.hom)
  rst_comm f g := Hom.ext (rst_comm f.hom g.hom)
  rst_comp_rst f g := Hom.ext (rst_comp_rst f.hom g.hom)
  rst_comp f g := Hom.ext (rst_comp f.hom g.hom)

@[simp] theorem restriction_hom {X Y : SplitObject C} (f : X ⟶ Y) :
    (rst f).hom = rst f.hom := rfl

variable [HasZeroMorphisms C]

instance : HasZeroMorphisms (SplitObject C) where
  zero X Y := ⟨⟨0, comp_zero, zero_comp⟩⟩
  comp_zero := by intros; exact Hom.ext comp_zero
  zero_comp := by intros; exact Hom.ext zero_comp

@[simp] theorem zero_hom (X Y : SplitObject C) : (0 : X ⟶ Y).hom = 0 := rfl

instance [RestrictionZero C] : RestrictionZero (SplitObject C) where
  restrict_zero X Y := Hom.ext (RestrictionZero.restrict_zero X.base Y.base)

end SplitObject

variable {C}

/-- The fully faithful inclusion sends `X` to `(X,1_X)`. -/
def splittingInclusion : C ⥤ SplitObject C where
  obj X := ⟨X, ⊤⟩
  map f := ⟨f, Category.id_comp f, Category.comp_id f⟩

namespace SplitObject

def baseIdem {X : SplitObject C} (a : Idem X) : Idem X.base :=
  ⟨a.hom.hom, congrArg Hom.hom a.restriction⟩

theorem baseIdem_le {X : SplitObject C} (a : Idem X) : baseIdem a ≤ X.domain :=
  a.hom.target

def relativeIdem {X : SplitObject C} (a : Idem X.base) (ha : a ≤ X.domain) : Idem X :=
  ⟨⟨a.hom, by rw [Idem.comm]; exact ha, ha⟩, Hom.ext a.restriction⟩

@[simp] theorem base_relative {X : SplitObject C} (a : Idem X.base)
    (ha : a ≤ X.domain) : baseIdem (relativeIdem a ha) = a := rfl

theorem baseIdem_injective {X : SplitObject C} : Function.Injective (baseIdem (X := X)) := by
  intro a b h
  apply Idem.ext
  apply Hom.ext
  exact congrArg Idem.hom h

theorem le_iff_base {X : SplitObject C} (a b : Idem X) :
    a ≤ b ↔ baseIdem a ≤ baseIdem b := by
  constructor
  · intro h
    exact congrArg Hom.hom (Idem.le_def.mp h)
  · intro h
    apply Idem.le_def.mpr
    exact Hom.ext h

@[simp] theorem base_inf {X : SplitObject C} (a b : Idem X) :
    baseIdem (a ⊓ b) = baseIdem a ⊓ baseIdem b := rfl

@[simp] theorem base_pull {X Y : SplitObject C} (f : X ⟶ Y) (a : Idem Y) :
    baseIdem (Idem.pull f a) = Idem.pull f.hom (baseIdem a) := rfl

@[simp] theorem base_top {X : SplitObject C} : baseIdem (⊤ : Idem X) = X.domain := rfl

instance [Ranges C] : Ranges (SplitObject C) where
  range f := relativeIdem (Ranges.range f.hom) (Ranges.least f.hom _ f.target)
  receives f := Hom.ext (Ranges.receives f.hom)
  agreement f g h he := Hom.ext
    (Ranges.agreement f.hom g.hom h.hom (congrArg Hom.hom he))

variable [BinaryJoins C]

instance : BinaryJoins (SplitObject C) where
  join a b := relativeIdem (baseIdem a ⊔ baseIdem b)
    (sup_le (baseIdem_le a) (baseIdem_le b))
  le_left _a _b := (le_iff_base _ _).mpr le_sup_left
  le_right _a _b := (le_iff_base _ _).mpr le_sup_right
  least _a _b _c ha hb := (le_iff_base _ _).mpr
    (sup_le ((le_iff_base _ _).mp ha) ((le_iff_base _ _).mp hb))

@[simp] theorem base_sup {X : SplitObject C} (a b : Idem X) :
    baseIdem (a ⊔ b) = baseIdem a ⊔ baseIdem b := rfl

instance [JoinInverse C] : JoinInverse (SplitObject C) where
  pull_sup f a b := by
    apply baseIdem_injective
    rw [base_pull, base_sup, JoinInverse.pull_sup, base_sup, base_pull, base_pull]

variable [HasZeroMorphisms C] [RestrictionZero C]

omit [BinaryJoins C] in
@[simp] theorem base_bot {X : SplitObject C} : baseIdem (⊥ : Idem X) = ⊥ := rfl

/-- Restriction idempotents on an included object are exactly the original
restriction idempotents, with the same order, meet, join, zero and identity. -/
def includedIdem {X : C} (a : Idem X) : Idem ((splittingInclusion (C := C)).obj X) :=
  relativeIdem a le_top

theorem inclusion_inseparable {X : C} {a b : Idem X} (h : Inseparable a b) :
    Inseparable (includedIdem a) (includedIdem b) := by
  constructor
  · apply baseIdem_injective
    change a ⊓ b = ⊥
    exact h.disjoint
  · rintro ⟨c, c', hc, ha, hb⟩
    apply h.no_separator
    refine ⟨baseIdem c, baseIdem c', ⟨?_, ?_⟩,
      (le_iff_base _ _).mp ha, (le_iff_base _ _).mp hb⟩
    · have he := congrArg baseIdem hc.disjoint
      change baseIdem c ⊓ baseIdem c' = ⊥ at he
      exact he
    · have he := congrArg baseIdem hc.cover
      change baseIdem c ⊔ baseIdem c' = ⊤ at he
      exact he

end SplitObject

end CategoricalEssentialIncompleteness.LocalConnectedness
