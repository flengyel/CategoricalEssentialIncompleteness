/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedFirstOrderIncompleteness

/-! # Statement checks for SignedFirstOrderIncompleteness -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

open LocalConnectedness
variable {C : Type u} [Category.{v} C] [RestrictionCategory C]
variable [Splits C] [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C]
variable [Regular (RestrictionSubobjects.Tot C)] [FinitaryExtensive (RestrictionSubobjects.Tot C)]
example (inverses : RestrictionSubobjects.MonoInverses C)
    {V X : RestrictionSubobjects.Tot C} (F : NullaryPresentations V)
    (a b : Subobject X) (hab : a ⊓ b = ⊥)
    (hc : (F.presentation X).Consistent (SignedFirstOrder.theory F a b).val) :
    (F.presentation X).EssentiallyIncomplete (SignedFirstOrder.theory F a b) ↔
      Inseparable (RestrictionSubobjects.domain inverses a)
        (RestrictionSubobjects.domain inverses b) :=
  SignedFirstOrder.essential_incomplete_iff_inseparable inverses F a b hab hc

#print axioms CategoricalEssentialIncompleteness.V46.SignedFirstOrder.essential_incomplete_iff_inseparable
