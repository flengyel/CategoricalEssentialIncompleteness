/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46BooleanFibers

/-! # Statement checks for BooleanFibers -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
example {W : D} (A : Subobject W) (b : W ⟶ Two D) (c : Bool) :
    A ≤ V46.Two.fiberSubobject b c ↔ A.arrow ≫ b = Two.constant _ c :=
  V46.Two.le_fiber_iff A b c

example {W : D} (b : W ⟶ Two D) :
    V46.Two.fiberSubobject (Two.unary Bool.not b) true = V46.Two.fiberSubobject b false :=
  V46.Two.not_fiber_true b

#print axioms CategoricalEssentialIncompleteness.V46.Two.fiber_arrow_value
#print axioms CategoricalEssentialIncompleteness.V46.Two.le_fiber_iff
#print axioms CategoricalEssentialIncompleteness.V46.Two.not_fiber_true
