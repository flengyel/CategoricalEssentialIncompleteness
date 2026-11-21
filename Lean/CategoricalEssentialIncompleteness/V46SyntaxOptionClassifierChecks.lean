/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxOptionClassifier


/-! # The Boolean classifier of an option's success pullback -/

@[expose] public section
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxOptionClassifierChecks
open SyntaxOptionTransport
variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]
example (Y : C) : IsPullback (coprod.inr : Y ⟶ OptionSyntax.obj Y) (terminal.from Y)
    (optionTag Y) (Two.point (C := C) true) := optionTag_isPullback Y
example {X Y : C} (f : X ⟶ OptionSyntax.obj Y) :
    IsPullback (pullback.fst f (coprod.inr : Y ⟶ OptionSyntax.obj Y))
      (terminal.from (pullback f (coprod.inr : Y ⟶ OptionSyntax.obj Y)))
      (f ≫ optionTag Y) (Two.point (C := C) true) := optionTag_success_isPullback f
example {X Y : C} (f : X ⟶ OptionSyntax.obj Y) :
    (Subobject.pullback (f ≫ optionTag Y)).obj (Subobject.mk (Two.point (C := C) true)) =
      OptionSyntax.success f := optionTag_success_subobject f
end CategoricalEssentialIncompleteness.V46.SyntaxOptionClassifierChecks
