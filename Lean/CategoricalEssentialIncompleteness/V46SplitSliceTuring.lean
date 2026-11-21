/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SliceProductTuring
public import CategoricalEssentialIncompleteness.V46PartialSliceRetractions
public import CategoricalEssentialIncompleteness.V46PartialSliceSplitting

/-! # Universal objects in partial slices of a split recursion category -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.SplitSliceTuring

open RestrictionSubobjects RecursionCategory

variable {R : Type u} [Category.{v} R] [PCategoryStruct R] [PCategory R]
variable [HasZeroMorphisms R] [Prodominical R] [Isotype R]

attribute [local instance] SplitObject.productData SplitObject.productLaws SplitObject.productSplits

local instance baseRestriction : RestrictionCategory (SplitObject R) :=
  @PCategory.inducedRestriction (SplitObject R) inferInstance
    SplitObject.productData SplitObject.productLaws

variable [HasPullbacks (Tot (SplitObject R))]
variable (inverses : MonoInverses (SplitObject R)) (T : Tot (SplitObject R))

/-- The original index object is universal in every partial slice. Both the total
parameter and each total embedding are morphisms of that slice; the evaluator uses its
complete binary product structure. -/
theorem turing_object (rec : PRecursionCategory R) :
    let Q := (splittingInclusion (C := R)).obj rec.W
    ∃ τ : nearProd Q Q ⟶ Q, IsTuringMorphism τ ∧
      @IsTuringMorphism (PartialMaps.Par (Over T)) inferInstance
        (PartialSliceProducts.pcategoryStruct inverses T)
        (PartialSliceProducts.pcategoryLaws inverses T)
        (PartialSliceTuring.constantObject T Q) (PartialSliceTuring.constantObject T Q)
        (PartialSliceTuring.constantObject T Q) (SliceProductTuring.evaluator inverses T τ) ∧
      ∀ X : PartialMaps.Par (Over T),
        ∃ (j : X ⟶ PartialSliceTuring.constantObject T Q)
          (s : PartialSliceTuring.constantObject T Q ⟶ X),
          isTotal j ∧ j ≫ s = 𝟙 X ∧ s ≫ j = CategoryTheory.RestrictionCategory.rst s := by
  dsimp only
  let Q := (splittingInclusion (C := R)).obj rec.W
  obtain ⟨τ, hτ⟩ := SplitTuring.turingFamily rec Q Q
  have hQ : ∀ Y : SplitObject R, ∃ (m : Y ⟶ Q) (r : Q ⟶ Y),
      isTotal m ∧ m ≫ r = 𝟙 Y := by
    intro Y
    obtain ⟨m, r, hm, hmr⟩ := SplitTuring.exists_total_retract rec.W Y
    refine ⟨m, r, ?_, hmr⟩
    change @PCategoryStruct.rst (SplitObject R) inferInstance SplitObject.productData Y Q m = 𝟙 Y
    rw [SplitObject.productData_restriction]
    exact hm
  exact ⟨τ, hτ, SliceProductTuring.evaluator_isTuring inverses T τ hτ,
    PartialSliceRetractions.exists_total_retract inverses T hQ⟩

end CategoricalEssentialIncompleteness.V46.SplitSliceTuring
