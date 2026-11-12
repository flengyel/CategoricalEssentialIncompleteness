/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SubobjectInseparability

/-! # Statement checks for SubobjectInseparability -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
example {X : D} (a b : Subobject X) :
    HasSubobjectSeparator a b ↔ ∃ d : X ⟶ Two D,
      a.arrow ≫ d = Two.constant _ true ∧ b.arrow ≫ d = Two.constant _ false :=
  subobject_separator_iff_boolean a b

#print axioms CategoricalEssentialIncompleteness.V46.subobject_separator_iff_boolean
#print axioms CategoricalEssentialIncompleteness.V46.subobject_separator_pullback
#print axioms CategoricalEssentialIncompleteness.V46.subobject_separator_mono
