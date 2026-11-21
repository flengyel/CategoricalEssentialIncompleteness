/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46CompatibleSplitSlices

/-! # Partial slices with a proved source restriction comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46
open RestrictionSubobjects

namespace CompatiblePartialSlices
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable [ρ : RestrictionCategory C] (hρ : PCategory.inducedRestriction = ρ)
variable [Splits C] [HasPullbacks (Tot C)]

theorem postcompose_restriction {T U : Tot C} (i : T ⟶ U) :
    PreservesRestriction (postcompose hρ i) := by
  subst ρ
  exact PartialSliceChangeBase.postcompose_restriction i
end CompatiblePartialSlices

namespace NativeSplitSlices
theorem restriction_ext {C : Type u} [Category.{v} C] (r s : RestrictionCategory C)
    (h : ∀ {X Y : C} (f : X ⟶ Y),
      @CategoryTheory.RestrictionCategory.rst C inferInstance r X Y f =
        @CategoryTheory.RestrictionCategory.rst C inferInstance s X Y f) : r = s := by
  cases r with
  | mk rr r1 r2 r3 r4 =>
    cases s with
    | mk rs s1 s2 s3 s4 =>
      have he : @rr = @rs := by
        funext X Y f
        exact h f
      cases he
      rfl

variable {R : Type u} [Category.{v} R] [PCategoryStruct R] [PCategory R]
variable [ρ : RestrictionCategory R] (hρ : PCategory.inducedRestriction = ρ)
variable [Splits (SplitObject R)] [HasPullbacks (Tot (SplitObject R))]
variable (inverses : MonoInverses (SplitObject R))

/-- The functor and its full retraction consequences are constructed in the source
restriction structure. -/
def constantData {Z U : Tot (SplitObject R)} (point : Z ⟶ U) (hZ : IsTerminal Z) :
    {K : SplitObject R ⥤ PartialMaps.Par (Over U) //
      K.Faithful ∧ PreservesRestriction K ∧
      ∀ {X Y : SplitObject R} (f : X ⟶ Y),
        RestrictionRetraction.HasTotalExtension (K.map f) ↔
          RestrictionRetraction.HasTotalExtension f} := by
  subst ρ
  let δ : RestrictionCategory (SplitObject R) := inferInstance
  letI : PCategoryStruct (SplitObject R) := SplitObject.productData
  letI : PCategory (SplitObject R) := SplitObject.productLaws
  letI : RestrictionCategory (SplitObject R) := δ
  exact CompatiblePartialSlices.constantData (ρ := δ) SplitObject.productRestriction_eq
    inverses point hZ

/-- This is the postcomposition functor, with its restriction law and proper-inclusion
obstruction retained together. -/
def postcomposeData {T U : Tot (SplitObject R)} (i : T ⟶ U) [Mono i] :
    {K : PartialMaps.Par (Over T) ⥤ PartialMaps.Par (Over U) //
      K.Full ∧ K.Faithful ∧ PreservesRestriction K ∧ (¬ IsIso i → ¬ K.EssSurj)} := by
  subst ρ
  let δ : RestrictionCategory (SplitObject R) := inferInstance
  letI : PCategoryStruct (SplitObject R) := SplitObject.productData
  letI : PCategory (SplitObject R) := SplitObject.productLaws
  letI : RestrictionCategory (SplitObject R) := δ
  exact ⟨CompatiblePartialSlices.postcompose (ρ := δ) SplitObject.productRestriction_eq i,
    CompatiblePartialSlices.postcompose_full (ρ := δ) SplitObject.productRestriction_eq inverses i,
    CompatiblePartialSlices.postcompose_faithful (ρ := δ) SplitObject.productRestriction_eq inverses i,
    CompatiblePartialSlices.postcompose_restriction (ρ := δ) SplitObject.productRestriction_eq i,
    CompatiblePartialSlices.postcompose_not_essSurj (ρ := δ) SplitObject.productRestriction_eq inverses i⟩

variable [HasZeroMorphisms R] [RecursionCategory.Prodominical R] [RecursionCategory.Isotype R]

def turingData (T : Tot (SplitObject R)) (rec : RecursionCategory.PRecursionCategory R) :
    CompatibleSplitSlices.TuringData (PartialMaps.Par (Over T)) := by
  subst ρ
  let δ : RestrictionCategory (SplitObject R) := inferInstance
  letI : PCategoryStruct (SplitObject R) := SplitObject.productData
  letI : PCategory (SplitObject R) := SplitObject.productLaws
  letI : RestrictionCategory (SplitObject R) := δ
  exact CompatibleSplitSlices.turingData (ρ := δ) SplitObject.productRestriction_eq inverses T rec

end NativeSplitSlices
end CategoricalEssentialIncompleteness.V46
