/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SplitProductCategory

/-! # Turing parameterization for arbitrary restriction splittings -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.RestrictionCategory
open PCategoryStruct RecursionCategory

namespace CategoricalEssentialIncompleteness.V46.SplitTuring

variable {R : Type u} [Category.{v} R] [PCategoryStruct R] [PCategory R]

/-- Changing input and output by isomorphisms retains Turing parameterization. -/
theorem retype {W X Y X' Y' : R} (τ : nearProd W X ⟶ Y)
    (hτ : IsTuringMorphism τ) (i : X' ≅ X) (j : Y ≅ Y') :
    IsTuringMorphism (nearProd_map (𝟙 W) i.hom ≫ τ ≫ j.hom) := by
  intro V φ
  obtain ⟨g, hg, hcode⟩ := hτ V (nearProd_map (𝟙 V) i.inv ≫ φ ≫ j.inv)
  refine ⟨g, hg, ?_⟩
  calc
    _ = (nearProd_map (𝟙 V) i.hom ≫ nearProd_map g (𝟙 X)) ≫ τ ≫ j.hom := by
      simp only [← Category.assoc, PCategory.nearProd_comp,
        Category.comp_id, Category.id_comp]
    _ = nearProd_map (𝟙 V) i.hom ≫
        (nearProd_map (𝟙 V) i.inv ≫ φ ≫ j.inv) ≫ j.hom := by
      simpa only [Category.assoc] using
        congrArg (fun k => nearProd_map (𝟙 V) i.hom ≫ k ≫ j.hom) hcode
    _ = φ := by
      have hi : nearProd_map (𝟙 V) i.hom ≫ nearProd_map (𝟙 V) i.inv =
          𝟙 (nearProd V X') := by
        rw [PCategory.nearProd_comp, Category.id_comp, i.hom_inv_id, PCategory.nearProd_id]
      simpa only [Category.assoc] using
        (show (nearProd_map (𝟙 V) i.hom ≫ nearProd_map (𝟙 V) i.inv) ≫
            φ ≫ (j.inv ≫ j.hom) = φ by
          rw [hi, j.inv_hom_id, Category.id_comp, Category.comp_id])

open CategoricalEssentialIncompleteness.LocalConnectedness
open SplitObject

attribute [local instance] SplitObject.productData SplitObject.productLaws

/-- The evaluator restricted to the chosen input and output domains. -/
def evaluator {W : R} (X Y : SplitObject R) (τ : nearProd W X.base ⟶ Y.base) :
    binaryProduct ((splittingInclusion (C := R)).obj W) X ⟶ Y where
  hom := nearProd_map (𝟙 W) X.domain.hom ≫ τ ≫ Y.domain.hom
  source := by
    change nearProd_map (𝟙 W) X.domain.hom ≫
      (nearProd_map (𝟙 W) X.domain.hom ≫ τ ≫ Y.domain.hom) = _
    rw [← Category.assoc, PCategory.nearProd_comp, Category.id_comp, X.domain.idem]
  target := by
    change (nearProd_map (𝟙 W) X.domain.hom ≫ τ ≫ Y.domain.hom) ≫ Y.domain.hom = _
    rw [Category.assoc, Category.assoc, Y.domain.idem]

/-- A total base parameter becomes total relative to the split source domain. -/
def parameter {W : R} (V : SplitObject R) (g : V.base ⟶ W) :
    V ⟶ (splittingInclusion (C := R)).obj W where
  hom := V.domain.hom ≫ g
  source := by rw [← Category.assoc, V.domain.idem]
  target := Category.comp_id _

theorem parameter_total {W : R} (V : SplitObject R) (g : V.base ⟶ W)
    (hg : isTotal g) :
    @PCategoryStruct.rst (SplitObject R) inferInstance productData
      V ((splittingInclusion (C := R)).obj W) (parameter V g) = 𝟙 V := by
  rw [productData_restriction]
  apply Hom.ext
  change CategoryTheory.RestrictionCategory.rst (V.domain.hom ≫ g) = V.domain.hom
  rw [rst_comp_of_isTotal _ hg, V.domain.restriction]

/-- The original universal evaluator parametrizes all partial morphisms
between arbitrary split objects. -/
theorem evaluator_isTuring {W : R} (X Y : SplitObject R)
    (τ : nearProd W X.base ⟶ Y.base) (hτ : IsTuringMorphism τ) :
    IsTuringMorphism (evaluator X Y τ) := by
  intro V φ
  obtain ⟨g, hg, hcode⟩ := hτ V.base φ.hom
  refine ⟨parameter V g, parameter_total V g hg, ?_⟩
  apply Hom.ext
  change nearProd_map (V.domain.hom ≫ g) X.domain.hom ≫
    (nearProd_map (𝟙 W) X.domain.hom ≫ τ ≫ Y.domain.hom) = φ.hom
  calc
    _ = (nearProd_map (V.domain.hom ≫ g) X.domain.hom) ≫ τ ≫ Y.domain.hom := by
      rw [← Category.assoc, PCategory.nearProd_comp, Category.comp_id, X.domain.idem]
    _ = nearProd_map V.domain.hom X.domain.hom ≫
        (nearProd_map g (𝟙 X.base) ≫ τ) ≫ Y.domain.hom := by
      simp only [← Category.assoc, PCategory.nearProd_comp, Category.comp_id]
    _ = φ.hom := by
      rw [hcode]
      change (binaryProduct V X).domain.hom ≫ φ.hom ≫ Y.domain.hom = φ.hom
      have hs : (binaryProduct V X).domain.hom ≫ φ.hom = φ.hom := φ.source
      rw [← Category.assoc, hs, φ.target]

/-- The partial retraction along an isomorphism of the underlying object. -/
def retract {Q : R} (X : SplitObject R) (i : X.base ≅ Q) :
    (splittingInclusion (C := R)).obj Q ⟶ X where
  hom := i.inv ≫ X.domain.hom
  source := Category.id_comp _
  target := by rw [Category.assoc, X.domain.idem]

theorem parameter_retract {Q : R} (X : SplitObject R) (i : X.base ≅ Q) :
    parameter X i.hom ≫ retract X i = 𝟙 X := by
  apply Hom.ext
  change (X.domain.hom ≫ i.hom) ≫ (i.inv ≫ X.domain.hom) = X.domain.hom
  rw [Category.assoc, ← Category.assoc i.hom, i.hom_inv_id, Category.id_comp, X.domain.idem]

theorem iso_parameter_total {Q : R} (X : SplitObject R) (i : X.base ≅ Q) :
    isTotal (parameter X i.hom) := by
  have hi : isTotal i.hom := by
    change CategoryTheory.RestrictionCategory.rst i.hom = 𝟙 X.base
    have h := congrArg (fun k => k ≫ i.inv)
      (CategoryTheory.RestrictionCategory.rst_comp_self i.hom)
    simpa only [Category.assoc, i.hom_inv_id, Category.comp_id] using h
  apply Hom.ext
  change CategoryTheory.RestrictionCategory.rst (X.domain.hom ≫ i.hom) = X.domain.hom
  rw [rst_comp_of_isTotal _ hi, X.domain.restriction]

variable [Isotype R]

/-- Every split object embeds totally into any fixed original object. -/
theorem exists_total_retract (Q : R) (X : SplitObject R) :
    ∃ (m : X ⟶ (splittingInclusion (C := R)).obj Q)
      (r : (splittingInclusion (C := R)).obj Q ⟶ X),
      isTotal m ∧ m ≫ r = 𝟙 X := by
  obtain ⟨i⟩ := Isotype.iso X.base Q
  exact ⟨parameter X i.hom, retract X i, iso_parameter_total X i, parameter_retract X i⟩

variable [CategoryTheory.Limits.HasZeroMorphisms R] [Prodominical R]

/-- The fixed index object of a recursion category works for all input and
output objects after restriction splitting. -/
theorem turingFamily (T : PRecursionCategory R) (X Y : SplitObject R) :
    ∃ τ : nearProd ((splittingInclusion (C := R)).obj T.W) X ⟶ Y, IsTuringMorphism τ := by
  obtain ⟨i⟩ := Isotype.iso X.base T.X
  obtain ⟨j⟩ := Isotype.iso T.Y Y.base
  exact ⟨evaluator X Y (nearProd_map (𝟙 T.W) i.hom ≫ T.tau ≫ j.hom),
    evaluator_isTuring X Y _ (retype T.tau T.is_turing i j)⟩

/-- A universal object and evaluator in the restriction splitting. -/
theorem turing_object (T : PRecursionCategory R) :
    ∃ (Q : SplitObject R) (τ : nearProd Q Q ⟶ Q),
      IsTuringMorphism τ ∧
      ∀ X : SplitObject R, ∃ (m : X ⟶ Q) (r : Q ⟶ X),
        isTotal m ∧ m ≫ r = 𝟙 X := by
  let Q := (splittingInclusion (C := R)).obj T.W
  obtain ⟨τ, hτ⟩ := turingFamily T Q Q
  exact ⟨Q, τ, hτ, exists_total_retract T.W⟩

end CategoricalEssentialIncompleteness.V46.SplitTuring
