/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedBooleanExtension

/-! # Statement checks for SignedBooleanExtension -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D} (F : NullaryPresentations V)
open SignedFirstOrder
example (d : X ⟶ Two D) (a b : Subobject X) (h : Separates d a b) :
    (theory F a b).val ≤ (booleanTheory F d).val := booleanTheory_extends F d a b h
example (d : X ⟶ Two D) : (F.presentation X).Consistent (booleanTheory F d).val :=
  booleanTheory_consistent F d

#print axioms CategoricalEssentialIncompleteness.V46.SignedFirstOrder.booleanTheory
#print axioms CategoricalEssentialIncompleteness.V46.SignedFirstOrder.booleanTheory_consistent
#print axioms CategoricalEssentialIncompleteness.V46.SignedFirstOrder.booleanTheory_complete
#print axioms CategoricalEssentialIncompleteness.V46.SignedFirstOrder.booleanTheory_contains_axioms
#print axioms CategoricalEssentialIncompleteness.V46.SignedFirstOrder.booleanTheory_extends
