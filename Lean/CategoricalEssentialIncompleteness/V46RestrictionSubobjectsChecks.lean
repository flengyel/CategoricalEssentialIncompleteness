/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RestrictionSubobjects

/-! # Statement checks for RestrictionSubobjects -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {C : Type u} [Category.{v} C] [RestrictionCategory C] [LocalConnectedness.Splits C]
open RestrictionSubobjects
variable (h : MonoInverses C)
example (X : Tot C) : Subobject X ≃o LocalConnectedness.Idem X.obj := orderIso h X
example {X : Tot C} (a b : Subobject X) : domain h a ≤ domain h b ↔ a ≤ b :=
  domain_le_iff h a b

#print axioms CategoricalEssentialIncompleteness.V46.RestrictionSubobjects.domain_le_iff_fixed
#print axioms CategoricalEssentialIncompleteness.V46.RestrictionSubobjects.domain_le_iff
#print axioms CategoricalEssentialIncompleteness.V46.RestrictionSubobjects.domain_surjective
#print axioms CategoricalEssentialIncompleteness.V46.RestrictionSubobjects.orderIso
