/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46PartialSliceChangeBase
public import CategoricalEssentialIncompleteness.V46AssociatedEvaluation

/-! # Partial slices under a proved equality of restriction structures -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.CompatiblePartialSlices
open RestrictionSubobjects
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable [ρ : RestrictionCategory C] (hρ : PCategory.inducedRestriction = ρ)
variable [Splits C] [HasPullbacks (Tot C)]

def postcompose {T U : Tot C} (i : T ⟶ U) :
    PartialMaps.Par (Over T) ⥤ PartialMaps.Par (Over U) := by
  subst ρ
  exact PartialSliceChangeBase.postcompose i

theorem postcompose_full (inverses : MonoInverses C) {T U : Tot C} (i : T ⟶ U) [Mono i] :
    (postcompose (ρ := ρ) hρ i).Full := by
  subst ρ
  exact PartialSliceChangeBase.postcompose_full i inverses

theorem postcompose_faithful (inverses : MonoInverses C) {T U : Tot C} (i : T ⟶ U) [Mono i] :
    (postcompose (ρ := ρ) hρ i).Faithful := by
  subst ρ
  exact PartialSliceChangeBase.postcompose_faithful i inverses

theorem postcompose_not_essSurj (inverses : MonoInverses C) {T U : Tot C} (i : T ⟶ U) [Mono i]
    (proper : ¬ IsIso i) : ¬ (postcompose (ρ := ρ) hρ i).EssSurj := by
  subst ρ
  exact PartialSliceChangeBase.not_essSurj i inverses proper

/-- The old retraction and both total-extension directions are transported together,
retaining the constant-family functor. -/
def constantData (inverses : MonoInverses C) {Z U : Tot C}
    (point : Z ⟶ U) (hZ : IsTerminal Z) :
    {K : C ⥤ PartialMaps.Par (Over U) //
      K.Faithful ∧ PreservesRestriction K ∧
        ∀ {X Y : C} (f : X ⟶ Y),
          RestrictionRetraction.HasTotalExtension (K.map f) ↔
            RestrictionRetraction.HasTotalExtension f} := by
  subst ρ
  exact ⟨PartialSliceTheoryFamilies.constantFunctor inverses U,
    AssociatedCategory.constant_faithful inverses point hZ,
    AssociatedCategory.constant_restriction inverses U,
    fun f => AssociatedCategory.hasTotalExtension_iff inverses point hZ f⟩

end CategoricalEssentialIncompleteness.V46.CompatiblePartialSlices
