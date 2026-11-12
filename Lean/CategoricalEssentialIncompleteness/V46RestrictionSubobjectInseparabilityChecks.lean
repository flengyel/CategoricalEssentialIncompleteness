/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RestrictionSubobjectInseparability

/-! # Statement checks for RestrictionSubobjectInseparability -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

open LocalConnectedness RestrictionSubobjects
variable {C : Type u} [Category.{v} C] [RestrictionCategory C]
variable [Splits C] [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C]
variable [Regular (Tot C)] [FinitaryExtensive (Tot C)]
example (h : MonoInverses C) {X : Tot C} (a b : Subobject X) :
    Inseparable (domain h a) (domain h b) ↔ SubobjectInseparable a b := inseparable_iff h a b

#print axioms CategoricalEssentialIncompleteness.V46.RestrictionSubobjects.complementary_iff
#print axioms CategoricalEssentialIncompleteness.V46.RestrictionSubobjects.inseparable_iff
