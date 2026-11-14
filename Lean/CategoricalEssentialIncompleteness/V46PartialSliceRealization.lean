/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSliceTuring
public import CategoricalEssentialIncompleteness.RestrictionFunctorEquivalences

/-! # The literal-family realization is full and faithful -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialSliceTuring

open RestrictionSubobjects
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable [Splits C] [HasPullbacks (Tot C)]
variable (inverses : MonoInverses C) (T : Tot C)

instance realization_faithful : (realization inverses T).Faithful where
  map_injective {X Y} f g he := by
    have h := congrArg (PartialSliceEquivalence.functor inverses T).map he
    rw [map_realization, map_realization] at h
    exact h

instance realization_full : (realization inverses T).Full where
  map_surjective f := by
    refine ⟨(PartialSliceEquivalence.functor inverses T).map f, ?_⟩
    apply (PartialSliceEquivalence.functor inverses T).map_injective
    rw [map_realization]

theorem realization_restriction : PreservesRestriction (realization inverses T) := by
  intro X Y f
  apply (PartialSliceEquivalence.functor inverses T).map_injective
  rw [map_realization, PartialSliceEquivalence.preserves_restrictions, map_realization]

end CategoricalEssentialIncompleteness.V46.PartialSliceTuring
