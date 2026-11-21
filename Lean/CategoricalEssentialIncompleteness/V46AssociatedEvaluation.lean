/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConstantFamilyRetraction
public import CategoricalEssentialIncompleteness.V46RestrictionRetraction
public import CategoricalEssentialIncompleteness.V46PartialSliceTheoryFamilies
public import CategoricalEssentialIncompleteness.V46PartialSliceSpanPullback

/-! # Evaluation of partial slices and the constant-family retraction -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.AssociatedCategory

open RestrictionSubobjects
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [HasPullbacks (Tot C)] (inverses : MonoInverses C)
variable {Z U : Tot C} (point : Z ⟶ U)

def evaluation : PartialMaps.Par (Over U) ⥤ C :=
  PartialSliceEquivalence.functor inverses U ⋙ ConstantFamilyRetraction.evaluation point

theorem evaluation_object (X : PartialMaps.Par (Over U)) :
    (evaluation inverses point).obj X = (pullback X.obj.hom point).obj := rfl

theorem evaluation_reindex : evaluation inverses point =
    PartialSliceChangeBase.reindex point inverses ⋙
      PartialSliceEquivalence.baseFunctor inverses Z := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change ((PartialSliceReindex.functor point).map
    ((PartialSliceEquivalence.functor inverses U).map f)).hom =
      ((PartialSliceEquivalence.functor inverses Z).map
        ((PartialSliceTuring.realization inverses Z).map
          ((PartialSliceReindex.functor point).map
            ((PartialSliceEquivalence.functor inverses U).map f)))).hom
  rw [PartialSliceTuring.map_realization]

theorem evaluation_spanPullback : evaluation inverses point =
    PartialSliceChangeBase.spanPullback point ⋙ PartialSliceEquivalence.baseFunctor inverses Z := by
  rw [evaluation_reindex, PartialSliceChangeBase.reindex_eq_spanPullback]

omit point in
theorem constant_restriction (P : Tot C) :
    PreservesRestriction (PartialSliceTheoryFamilies.constantFunctor inverses P) := by
  intro X Y f
  apply (PartialSliceEquivalence.functor inverses P).map_injective
  rw [PartialSliceTheoryFamilies.constant_value, PartialSliceEquivalence.preserves_restrictions,
    PartialSliceTheoryFamilies.constant_value]
  apply AmbientPartialSlice.Hom.ext
  change nearProd_map (𝟙 P.obj) (CategoryTheory.RestrictionCategory.rst f) =
    CategoryTheory.RestrictionCategory.rst (nearProd_map (𝟙 P.obj) f)
  have h := PCategory.rst_nearProd_map (𝟙 P.obj) f
  change CategoryTheory.RestrictionCategory.rst (nearProd_map (𝟙 P.obj) f) =
    nearProd_map (CategoryTheory.RestrictionCategory.rst (𝟙 P.obj))
      (CategoryTheory.RestrictionCategory.rst f) at h
  rw [rst_id] at h
  exact h.symm

theorem evaluation_restriction : PreservesRestriction (evaluation inverses point) := by
  intro X Y f
  change (ConstantFamilyRetraction.evaluation point).map
    ((PartialSliceEquivalence.functor inverses U).map (rst f)) = _
  rw [PartialSliceEquivalence.preserves_restrictions,
    ConstantFamilyRetraction.evaluation_restriction]
  rfl

variable (hZ : IsTerminal Z)

def retraction :
    PartialSliceTheoryFamilies.constantFunctor inverses U ⋙ evaluation inverses point ≅ 𝟭 C :=
  NatIso.ofComponents (fun X => (ConstantFamilyRetraction.retraction hZ point inverses).app X)
    (by
      intro X Y f
      change (ConstantFamilyRetraction.evaluation point).map
          ((PartialSliceEquivalence.functor inverses U).map
            ((PartialSliceTuring.realization inverses U).map
              ((ConstantFamilyProducts.constantFunctor U.obj).map f))) ≫ _ = _
      rw [PartialSliceTuring.map_realization]
      exact (ConstantFamilyRetraction.retraction hZ point inverses).hom.naturality f)

include point hZ in
theorem constant_faithful : (PartialSliceTheoryFamilies.constantFunctor inverses U).Faithful :=
  RestrictionRetraction.faithful _ _ (retraction inverses point hZ)

include point hZ in
theorem constant_total_iff {X Y : C} (f : X ⟶ Y) :
    isTotal ((PartialSliceTheoryFamilies.constantFunctor inverses U).map f) ↔ isTotal f :=
  RestrictionRetraction.total_iff _ _ (retraction inverses point hZ)
    (constant_restriction inverses U) f

include point hZ in
theorem hasTotalExtension_iff {X Y : C} (f : X ⟶ Y) :
    RestrictionRetraction.HasTotalExtension
        ((PartialSliceTheoryFamilies.constantFunctor inverses U).map f) ↔
      RestrictionRetraction.HasTotalExtension f :=
  RestrictionRetraction.hasTotalExtension_iff _ _ (retraction inverses point hZ)
    (constant_restriction inverses U) (evaluation_restriction inverses point) f

include point hZ in
theorem noTotalExtension_iff {X Y : C} (f : X ⟶ Y) :
    ¬ RestrictionRetraction.HasTotalExtension
        ((PartialSliceTheoryFamilies.constantFunctor inverses U).map f) ↔
      ¬ RestrictionRetraction.HasTotalExtension f :=
  not_congr (hasTotalExtension_iff inverses point hZ f)

end CategoricalEssentialIncompleteness.V46.AssociatedCategory
