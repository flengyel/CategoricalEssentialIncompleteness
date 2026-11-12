/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedSubobjectIncompleteness

/-! # Statement checks for SignedSubobjectIncompleteness -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D} (F : NullaryPresentations V)
example (a b : Subobject X) (hab : a ⊓ b = ⊥)
    (hc : (F.presentation X).Consistent (SignedFirstOrder.theory F a b).val) :
    (F.presentation X).EssentiallyIncomplete (SignedFirstOrder.theory F a b) ↔
      SubobjectInseparable a b :=
  SignedFirstOrder.essential_incomplete_iff_subobject_inseparable F a b hab hc

#print axioms CategoricalEssentialIncompleteness.V46.SignedFirstOrder.essential_incomplete_of_subobject_inseparable
#print axioms CategoricalEssentialIncompleteness.V46.SignedFirstOrder.no_subobject_separator_of_essential_incomplete
#print axioms CategoricalEssentialIncompleteness.V46.SignedFirstOrder.essential_incomplete_iff_subobject_inseparable
