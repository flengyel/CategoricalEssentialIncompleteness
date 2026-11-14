/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConstantSliceFull
public import CategoricalEssentialIncompleteness.V46SplitSliceTuring
public import CategoricalEssentialIncompleteness.V46RestrictionTerminal

/-! # Intended-statement checks for manuscript v57 Lemma 5.1 -/

@[expose] public section
noncomputable section

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46 RestrictionSubobjects RecursionCategory

section Completion

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
variable [RestrictionCategory A] [RestrictionCategory B] [Splits B]
variable (F : A ⥤ B) [F.Full] [F.Faithful] (hF : PreservesRestriction F)
variable (dense : ∀ Y : B, ∃ (X : A) (j : Y ⟶ F.obj X) (r : F.obj X ⟶ Y),
  isTotal j ∧ j ≫ r = 𝟙 Y ∧ r ≫ j = rst r)

example : SplitObject A ≌ B := RestrictionCompletion.equivalence F hF dense

example : PreservesRestriction (RestrictionCompletion.equivalence F hF dense).functor :=
  RestrictionCompletion.equivalence_restriction F hF dense

example : PreservesRestriction (RestrictionCompletion.equivalence F hF dense).inverse :=
  RestrictionCompletion.inverse_restriction _
    (RestrictionCompletion.equivalence_restriction F hF dense)

end Completion

section PartialSlices

variable {R : Type u₁} [Category.{v₁} R] [PCategoryStruct R] [PCategory R]
variable [HasZeroMorphisms R] [Prodominical R] [Isotype R]
attribute [local instance] SplitObject.productData SplitObject.productLaws SplitObject.productSplits

local instance baseRestriction : RestrictionCategory (SplitObject R) :=
  @PCategory.inducedRestriction (SplitObject R) inferInstance
    SplitObject.productData SplitObject.productLaws

variable [HasPullbacks (Tot (SplitObject R))]
variable (inverses : MonoInverses (SplitObject R)) (T : Tot (SplitObject R))

example (rec : PRecursionCategory R) :
    ∃ (Q : SplitObject R) (τ : nearProd Q Q ⟶ Q), IsTuringMorphism τ ∧
      ∀ X : SplitObject R, ∃ (m : X ⟶ Q) (r : Q ⟶ X),
        isTotal m ∧ m ≫ r = 𝟙 X := by
  obtain ⟨Q, τ, hτ, hQ⟩ := SplitTuring.turing_object rec
  refine ⟨Q, τ, hτ, ?_⟩
  intro X
  obtain ⟨m, r, hm, hmr⟩ := hQ X
  refine ⟨m, r, ?_, hmr⟩
  change @PCategoryStruct.rst (SplitObject R) inferInstance SplitObject.productData _ _ m = _
  rw [SplitObject.productData_restriction]
  exact hm

example [HasTerminal (Tot (SplitObject R))] :
    ∃ (Z : SplitObject R) (t : ∀ X : SplitObject R, X ⟶ Z),
      (∀ X, isTotal (t X)) ∧ t Z = 𝟙 Z ∧
      (∀ {X Y : SplitObject R} (f : X ⟶ Y),
        f ≫ t Y = CategoryTheory.RestrictionCategory.rst f ≫ t X) :=
  RestrictionTerminal.exists_restriction_terminal

example (rec : PRecursionCategory R) :
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
          isTotal j ∧ j ≫ s = 𝟙 X ∧ s ≫ j = rst s :=
  SplitSliceTuring.turing_object inverses T rec

example {X Y : PartialMaps.Par (Over T)} (f : X ⟶ Y) :
    f ≫ PartialSliceRetractions.terminate inverses T Y =
      rst f ≫ PartialSliceRetractions.terminate inverses T X :=
  PartialSliceRetractions.terminate_naturality inverses T f

example (rec : PRecursionCategory R) :
    @PRecursionCategory (ConstantSlice.Full.FullCategory T.obj) inferInstance
      (ConstantSlice.Full.productData T.obj) (ConstantSlice.Full.productLaws T.obj)
      inferInstance (ConstantSlice.Full.prodominical T.obj) (ConstantSlice.Full.isotype T.obj) :=
  ConstantSlice.Full.recursionCategory rec T.obj

example : @PCategory.inducedRestriction (ConstantSlice.Full.FullCategory T.obj) inferInstance
    (ConstantSlice.Full.productData T.obj) (ConstantSlice.Full.productLaws T.obj) =
      (inferInstance : RestrictionCategory (ConstantSlice.Full.FullCategory T.obj)) :=
  ConstantSlice.Full.productRestriction_eq T.obj

example (Q : R) :
    SplitObject (ConstantSlice.Full.FullCategory T.obj) ≌ PartialMaps.Par (Over T) :=
  ConstantSlice.Full.splittingEquivalence inverses T Q

example (Q : R) :
    PreservesRestriction (ConstantSlice.Full.splittingEquivalence inverses T Q).functor ∧
      PreservesRestriction (ConstantSlice.Full.splittingEquivalence inverses T Q).inverse :=
  ⟨ConstantSlice.Full.splittingEquivalence_restriction inverses T Q,
    ConstantSlice.Full.splittingEquivalence_inverse_restriction inverses T Q⟩

example (Z : PartialMaps.Par (Over T)) :
    (∃ X : ConstantSlice.Full.FullCategory T.obj,
      (ConstantSlice.Full.actualInclusion inverses T).obj X = Z) ↔
      ∃ X : R, PartialSliceTuring.constantObject T ((splittingInclusion (C := R)).obj X) = Z :=
  ConstantSlice.Full.actualInclusion_range inverses T Z

end PartialSlices

#print axioms RestrictionCompletion.extension
#print axioms RestrictionCompletion.extension_restriction
#print axioms RestrictionCompletion.extension_full
#print axioms RestrictionCompletion.extension_faithful
#print axioms RestrictionCompletion.extension_essSurj
#print axioms RestrictionCompletion.equivalence
#print axioms RestrictionCompletion.equivalence_restriction
#print axioms RestrictionCompletion.inverse_restriction
#print axioms FullRestrictionProducts.restrictionProducts
#print axioms FullRestrictionProducts.map_comparison
#print axioms FullRestrictionProducts.evaluator_isTuring
#print axioms ConstantFamilyProducts.associatorIso
#print axioms ConstantFamilyProducts.productIso
#print axioms PartialSliceTuring.realization_full
#print axioms PartialSliceTuring.realization_faithful
#print axioms PartialSliceTuring.realization_restriction
#print axioms RestrictionProducts.ProductData.prodominicalLaws
#print axioms AmbientProductTuring.evaluator_isTuring
#print axioms ConstantSlice.fullProductIso
#print axioms ConstantSlice.productLaws
#print axioms ConstantSlice.productRestriction_eq
#print axioms ConstantSlice.recursionCategory
#print axioms ConstantSlice.dense
#print axioms ConstantSlice.splittingEquivalence
#print axioms ConstantSlice.Full.productLaws
#print axioms ConstantSlice.Full.productRestriction_eq
#print axioms ConstantSlice.Full.prodominical
#print axioms ConstantSlice.Full.isotype
#print axioms ConstantSlice.Full.exists_evaluator
#print axioms ConstantSlice.Full.recursionCategory
#print axioms ConstantSlice.Full.actualInclusion_full
#print axioms ConstantSlice.Full.actualInclusion_faithful
#print axioms ConstantSlice.Full.actualInclusion_range
#print axioms ConstantSlice.Full.splittingEquivalence
#print axioms ConstantSlice.Full.splittingEquivalence_restriction
#print axioms ConstantSlice.Full.splittingEquivalence_inverse_restriction
#print axioms SplitTuring.turing_object
#print axioms SplitSliceTuring.turing_object
#print axioms RestrictionTerminal.exists_restriction_terminal
