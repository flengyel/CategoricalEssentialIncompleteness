/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalQuantifierAdmissibilityOptions
public import CategoricalEssentialIncompleteness.TwoBoolean

/-! # Subobjects defined by Boolean values -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.Two

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

@[reassoc] theorem fiber_arrow_value {W : D} (b : W ⟶ Two D) (c : Bool) :
    (fiberSubobject b c).arrow ≫ b = Two.constant _ c := by
  change (equalizerSubobject b (Two.constant W c)).arrow ≫ b = _
  rw [equalizerSubobject_arrow_comp, Two.comp_constant]
  rfl

theorem le_fiber_iff {W : D} (A : Subobject W) (b : W ⟶ Two D) (c : Bool) :
    A ≤ fiberSubobject b c ↔ A.arrow ≫ b = Two.constant _ c := by
  constructor
  · intro h
    have he := congrArg (fun f => f ≫ b) (Subobject.ofLE_arrow h)
    simpa only [Category.assoc, fiber_arrow_value, Two.comp_constant] using he.symm
  · intro h
    exact Subobject.le_mk_of_comm
      (equalizer.lift A.arrow (by rw [h, Two.comp_constant])) (equalizer.lift_ι _ _)

@[simp] theorem not_twice {W : D} (b : W ⟶ Two D) :
    Two.unary Bool.not (Two.unary Bool.not b) = b := by
  change bᶜᶜ = b
  exact compl_compl b

theorem not_fiber_true {W : D} (b : W ⟶ Two D) :
    fiberSubobject (Two.unary Bool.not b) true = fiberSubobject b false := by
  apply le_antisymm
  · apply (le_fiber_iff _ b false).mpr
    have h := congrArg (Two.unary Bool.not)
      (fiber_arrow_value (Two.unary Bool.not b) true)
    rw [← Two.comp_unary, not_twice, Two.unary_constant] at h
    exact h
  · apply (le_fiber_iff _ (Two.unary Bool.not b) true).mpr
    rw [Two.comp_unary, fiber_arrow_value, Two.unary_constant]
    rfl

end CategoricalEssentialIncompleteness.V46.Two
