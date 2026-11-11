/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransportBooleans


/-! # Statement checks in `V46SyntaxListOperationsTransportBooleansChecks` -/

@[expose] public section
noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open CategoricalEssentialIncompleteness.V46.DecidableVariables.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]

example (E : C ≌ D) {X : C} (f g : X ⟶ Two C) :
    E.functor.map (Two.binary Bool.or f g) ≫ (booleanIso E).hom =
      Two.binary Bool.or (E.functor.map f ≫ (booleanIso E).hom)
        (E.functor.map g ≫ (booleanIso E).hom) :=
  map_boolean_binary E Bool.or f g
