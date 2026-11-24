/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Splitting the idempotents of a full subcategory that split in the ambient category

The class in Cockett and Hofstra, Theorem 4.9(ii), can be taken to consist of all
idempotents on formal powers whose images split in the given Turing category.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Idempotents

namespace CategoricalEssentialIncompleteness.V46.IdempotentSplitting

universe v w u z
variable {B : Type u} {C : Type z} [Category.{v} B] [Category.{w} C] (F : B ⥤ C)

structure Splitting (P : Karoubi B) where
  obj : C
  i : obj ⟶ F.obj P.X
  r : F.obj P.X ⟶ obj
  section_retraction : i ≫ r = 𝟙 obj
  factor : r ≫ i = F.map P.p

attribute [reassoc] Splitting.section_retraction Splitting.factor

def splitsIn : ObjectProperty (Karoubi B) := fun P => Nonempty (Splitting F P)

theorem identity_mem (X : B) : splitsIn F ((toKaroubi B).obj X) :=
  ⟨⟨F.obj X, 𝟙 _, 𝟙 _, Category.id_comp _, by simp⟩⟩

noncomputable def splitting (P : (splitsIn F).FullSubcategory) : Splitting F P.obj :=
  Classical.choice P.property

noncomputable def realization : (splitsIn F).FullSubcategory ⥤ C where
  obj P := (splitting F P).obj
  map {P Q} f := (splitting F P).i ≫ F.map f.hom.f ≫ (splitting F Q).r
  map_id P := by
    change (splitting F P).i ≫ F.map P.obj.p ≫ (splitting F P).r = 𝟙 _
    rw [← (splitting F P).factor, ← Category.assoc (splitting F P).i,
      (splitting F P).section_retraction_assoc, (splitting F P).section_retraction]
  map_comp {P Q R} f g := by
    change _ ≫ F.map (f.hom.f ≫ g.hom.f) ≫ _ =
      (_ ≫ F.map f.hom.f ≫ (splitting F Q).r) ≫
        (splitting F Q).i ≫ F.map g.hom.f ≫ _
    rw [F.map_comp]
    simp only [Category.assoc, (splitting F Q).factor_assoc, ← F.map_comp_assoc,
      Karoubi.p_comp]

noncomputable def fullyFaithfulRealization (ff : F.FullyFaithful) : (realization F).FullyFaithful where
  preimage {P Q} h := ObjectProperty.homMk ⟨ff.preimage ((splitting F P).r ≫ h ≫ (splitting F Q).i), by
    let := ff.faithful
    apply F.map_injective
    simp only [F.map_comp, ff.map_preimage, ← (splitting F P).factor, ← (splitting F Q).factor,
      Category.assoc, (splitting F P).section_retraction_assoc, (splitting F Q).section_retraction_assoc]⟩
  map_preimage {P Q} h := by
    change (splitting F P).i ≫ F.map (ff.preimage _) ≫ (splitting F Q).r = h
    simp only [ff.map_preimage, Category.assoc, (splitting F P).section_retraction_assoc,
      (splitting F Q).section_retraction]
    exact Category.comp_id h
  preimage_map {P Q} h := by
    apply ObjectProperty.hom_ext
    apply Karoubi.hom_ext
    let := ff.faithful
    apply F.map_injective
    change F.map (ff.preimage ((splitting F P).r ≫
      ((splitting F P).i ≫ F.map h.hom.f ≫ (splitting F Q).r) ≫ (splitting F Q).i)) = _
    simp only [ff.map_preimage, Category.assoc, (splitting F P).factor_assoc,
      (splitting F Q).factor, ← F.map_comp, Karoubi.comp_p, Karoubi.p_comp]

theorem realization_essSurj (ff : F.FullyFaithful)
    (retracts : ∀ X : C, ∃ (b : B) (i : X ⟶ F.obj b) (r : F.obj b ⟶ X), i ≫ r = 𝟙 X) :
    (realization F).EssSurj := by
  constructor
  intro X
  let := ff.faithful
  obtain ⟨b, i, r, ir⟩ := retracts X
  have ri : F.map (ff.preimage (r ≫ i)) = r ≫ i := ff.map_preimage _
  let P : Karoubi B := ⟨b, ff.preimage (r ≫ i), F.map_injective (by
    rw [F.map_comp, ri]
    simp only [Category.assoc, ← Category.assoc i r, ir, Category.id_comp])⟩
  let Q : (splitsIn F).FullSubcategory := ⟨P, ⟨⟨X, i, r, ir, ri.symm⟩⟩⟩
  let s := splitting F Q
  have eqn : s.r ≫ s.i = r ≫ i := s.factor.trans ri
  refine ⟨Q, ⟨{ hom := s.i ≫ r, inv := i ≫ s.r, hom_inv_id := ?_, inv_hom_id := ?_ }⟩⟩
  · change (s.i ≫ r) ≫ i ≫ s.r = 𝟙 _
    rw [Category.assoc, ← Category.assoc r i, ← eqn, ← Category.assoc s.i,
      s.section_retraction_assoc, s.section_retraction]
  · change (i ≫ s.r) ≫ s.i ≫ r = 𝟙 X
    rw [Category.assoc, ← Category.assoc s.r s.i, eqn, Category.assoc r i, ir,
      Category.comp_id, ir]

/-- If every ambient object is a retract of an object in the image of a fully
faithful functor, splitting the idempotents in this class recovers the ambient category. -/
noncomputable def equivalence (ff : F.FullyFaithful)
    (retracts : ∀ X : C, ∃ (b : B) (i : X ⟶ F.obj b) (r : F.obj b ⟶ X), i ≫ r = 𝟙 X) :
    C ≌ (splitsIn F).FullSubcategory := by
  letI := (fullyFaithfulRealization F ff).full
  letI := (fullyFaithfulRealization F ff).faithful
  letI := realization_essSurj F ff retracts
  letI : (realization F).IsEquivalence := {}
  exact (realization F).asEquivalence.symm

end CategoricalEssentialIncompleteness.V46.IdempotentSplitting
