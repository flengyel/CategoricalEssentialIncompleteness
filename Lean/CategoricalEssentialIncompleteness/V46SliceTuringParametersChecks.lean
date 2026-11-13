/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SliceTuringParameters

/-! # Explicit slice parameter and retraction equations -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.RestrictionCategory PCategoryStruct RecursionCategory
open CategoricalEssentialIncompleteness.V46 SliceTuringParameters RestrictionSubobjects

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

example {X T Q : C} (τ : nearProd Q Q ⟶ Q) (hτ : IsTuringMorphism τ)
    (p : X ⟶ T) (hp : isTotal p) (φ : nearProd X Q ⟶ nearProd T Q)
    (hφ : φ ≫ p0 T Q = CategoryTheory.RestrictionCategory.rst φ ≫ (p0 X Q ≫ p)) :
    ∃ a : X ⟶ nearProd T Q, isTotal a ∧ a ≫ p0 T Q = p ∧
      nearProd_map a (𝟙 Q) ≫ assoc T Q Q ≫ nearProd_map (𝟙 T) τ = φ :=
  slice_parameterization τ hτ p hp φ hφ

example (inverses : MonoInverses C) {X T Q : C}
    (p : X ⟶ T) (hp : isTotal p) (m : X ⟶ Q) (hm : isTotal m)
    (r : Q ⟶ X) (hmr : m ≫ r = 𝟙 X) :
    ∃ (j : X ⟶ nearProd T Q) (s : nearProd T Q ⟶ X),
      isTotal j ∧ j ≫ p0 T Q = p ∧ j ≫ s = 𝟙 X ∧
      s ≫ j = CategoryTheory.RestrictionCategory.rst s ∧
      s ≫ p = CategoryTheory.RestrictionCategory.rst s ≫ p0 T Q :=
  total_retract_over inverses p hp m hm r hmr

#print axioms CategoricalEssentialIncompleteness.V46.SliceTuringParameters.evaluation_formula
#print axioms CategoricalEssentialIncompleteness.V46.SliceTuringParameters.slice_parameterization
#print axioms CategoricalEssentialIncompleteness.V46.SliceTuringParameters.total_retract_over
