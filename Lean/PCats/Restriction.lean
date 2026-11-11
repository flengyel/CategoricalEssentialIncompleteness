/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Restriction categories

Cockett-Lack restriction categories: Appendix A, section A.1, together with the
total-morphism material of section A.3 that does not mention the near product.

This module is independent of `PCategoryStruct`. Nothing below refers to
`P`-categories, and nothing above this module in the import graph should.

## Conventions

Composition is diagrammatic (`f ≫ g` applies `f` first); the appendix writes
`gf`. Every statement is the diagrammatic transcription of the appendix
equation cited in its doc comment.

Imports are inherited wholesale from the pre-split monolith and are wider than
this module needs; prune only after each module is known to build on its own.
-/

@[expose] public section

universe v u

namespace CategoryTheory

/-! ## 1. Restriction categories (Appendix A, §A.1) -/

/-- Cockett--Lack restriction category.  Field names track the four displayed
axioms `f rst f = f`, `rst f rst g = rst g rst f`, `rst(g rst f) = rst g rst f`,
`rst g f = f rst(gf)`. -/
class RestrictionCategory (C : Type u) [Category.{v} C] where
  rst : {X Y : C} → (X ⟶ Y) → (X ⟶ X)
  /-- R1: `f rst f = f`. -/
  rst_comp_self : ∀ {X Y : C} (f : X ⟶ Y), rst f ≫ f = f
  /-- R2: `rst f rst g = rst g rst f`. -/
  rst_comm : ∀ {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z), rst f ≫ rst g = rst g ≫ rst f
  /-- R3: `rst (g rst f) = rst g rst f`.  This is *not* idempotence; see
  `rst_idem` below. -/
  rst_comp_rst : ∀ {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z),
    rst (rst f ≫ g) = rst f ≫ rst g
  /-- R4: `rst g f = f rst (gf)`. -/
  rst_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), rst (f ≫ g) ≫ f = f ≫ rst g

namespace RestrictionCategory

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]

lemma rst_id (X : C) : rst (𝟙 X) = 𝟙 X := by
  simpa using rst_comp_self (𝟙 X)

/-- Idempotence of restriction idempotents, a consequence of R1 and R3. -/
lemma rst_idem {X Y : C} (f : X ⟶ Y) : rst f ≫ rst f = rst f := by
  have h := rst_comp_rst f f
  rw [rst_comp_self] at h
  exact h.symm

/-- `rst (gf) ≤ rst f` in the domain order. -/
lemma rst_comp_absorb {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    rst f ≫ rst (f ≫ g) = rst (f ≫ g) := by
  have h := rst_comp_rst f (f ≫ g)
  rw [← Category.assoc, rst_comp_self] at h
  exact h.symm

/-- Appendix A, line following the axioms: `rst (gf) = rst (rst g f)`. -/
lemma rst_comp_rst_right {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    rst (f ≫ g) = rst (f ≫ rst g) := by
  have h := congrArg rst (rst_comp f g)
  rw [rst_comp_rst (f ≫ g) f, rst_comm (f ≫ g) f, rst_comp_absorb f g] at h
  exact h

/-- Total morphisms (Appendix A, §A.3). -/
def isTotal : MorphismProperty C := fun X _ f => rst f = 𝟙 X

lemma isTotal_iff {X Y : C} (f : X ⟶ Y) : isTotal f ↔ rst f = 𝟙 X := Iff.rfl

/-- Appendix A: if `q` is total and `k : T ⟶ R`, then `rst (qk) = rst k`. -/
lemma rst_comp_of_isTotal {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} (hg : isTotal g) :
    rst (f ≫ g) = rst f := by
  rw [rst_comp_rst_right, show rst g = 𝟙 Y from hg, Category.comp_id]

lemma isTotal_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : isTotal f) (hg : isTotal g) : isTotal (f ≫ g) := by
  change rst (f ≫ g) = 𝟙 X
  rw [rst_comp_of_isTotal f hg]
  exact hf

instance : MorphismProperty.IsMultiplicative (isTotal (C := C)) where
  id_mem X := rst_id X
  comp_mem _ _ hf hg := isTotal_comp hf hg

/-- Split restriction category (Appendix A, §A.1, final paragraph). -/
class Split (C : Type u) [Category.{v} C] [RestrictionCategory C] where
  obj : {X : C} → (X ⟶ X) → C
  proj : {X : C} → (e : X ⟶ X) → (X ⟶ obj e)
  incl : {X : C} → (e : X ⟶ X) → (obj e ⟶ X)
  incl_proj : ∀ {X Y : C} (f : X ⟶ Y), proj (rst f) ≫ incl (rst f) = rst f
  proj_incl : ∀ {X Y : C} (f : X ⟶ Y), incl (rst f) ≫ proj (rst f) = 𝟙 (obj (rst f))
  incl_mono : ∀ {X Y : C} (f : X ⟶ Y), Mono (incl (rst f))

end RestrictionCategory
end CategoryTheory
