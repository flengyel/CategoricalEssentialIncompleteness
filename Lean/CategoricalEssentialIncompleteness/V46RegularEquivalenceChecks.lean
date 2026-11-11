/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RegularEquivalence

/-! Regularity is transported without split-epimorphism assumptions. -/

@[expose] public section
noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

example [HasFiniteLimits C] [HasFiniteLimits D] (E : C ≌ D)
    {X Y : C} (f : X ⟶ Y) :
    IsRegularEpi (E.functor.map f) ↔ IsRegularEpi f :=
  RegularEquivalence.regularEpi_iff E f

example [Regular C] [HasFiniteLimits D] (E : C ≌ D) : Regular D :=
  RegularEquivalence.regular E
