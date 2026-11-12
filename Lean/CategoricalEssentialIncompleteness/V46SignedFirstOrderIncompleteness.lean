/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedSubobjectIncompleteness
public import CategoricalEssentialIncompleteness.V46RestrictionSubobjectInseparability

/-! # Corollary 4.8: essential incompleteness of free signed theories -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.SignedFirstOrder

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]
variable [Splits C] [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C]
variable [Regular (RestrictionSubobjects.Tot C)] [FinitaryExtensive (RestrictionSubobjects.Tot C)]

/-- The Boolean extension gives the converse; the subobject/domain order
isomorphism identifies the two notions of inseparability. -/
theorem essential_incomplete_iff_inseparable
    (inverses : RestrictionSubobjects.MonoInverses C)
    {V X : RestrictionSubobjects.Tot C} (F : NullaryPresentations V)
    (a b : Subobject X) (hab : a ⊓ b = ⊥)
    (consistent : (F.presentation X).Consistent (theory F a b).val) :
    (F.presentation X).EssentiallyIncomplete (theory F a b) ↔
      Inseparable (RestrictionSubobjects.domain inverses a)
        (RestrictionSubobjects.domain inverses b) :=
  (essential_incomplete_iff_subobject_inseparable F a b hab consistent).trans
    (RestrictionSubobjects.inseparable_iff inverses a b).symm

end CategoricalEssentialIncompleteness.V46.SignedFirstOrder
