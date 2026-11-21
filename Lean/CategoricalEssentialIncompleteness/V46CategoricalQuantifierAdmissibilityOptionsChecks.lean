/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalQuantifierAdmissibilityOptions

/-! Option success is computed from categorical pullbacks. -/

@[expose] public section
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

example {X Y : D} (f : X ⟶ OptionSyntax.obj Y) :
    OptionSyntax.success f = Subobject.mk (pullback.fst f coprod.inr) :=
  OptionSyntax.success_eq_mk f

example {X Y Z : D} (k : X ⟶ OptionSyntax.obj Y) (f : Y ⟶ Z) :
    OptionSyntax.success (k ≫ OptionSyntax.map f) = OptionSyntax.success k :=
  OptionSyntax.success_map_comp k f

example {X V Y Z : D} (h : V ⨯ Y ⟶ Z) (k : X ⟶ V ⨯ OptionSyntax.obj Y) :
    OptionSyntax.success (k ≫ OptionSyntax.coefficient h) =
      OptionSyntax.success (k ≫ prod.snd) :=
  OptionSyntax.success_coefficient_comp h k

example {X Y : D} (b : X ⟶ Two D) (f g : X ⟶ OptionSyntax.obj Y) :
    OptionSyntax.success (Two.branch b f g) =
      (Two.fiberSubobject b false ⊓ OptionSyntax.success f) ⊔
        (Two.fiberSubobject b true ⊓ OptionSyntax.success g) :=
  OptionSyntax.success_branch b f g
