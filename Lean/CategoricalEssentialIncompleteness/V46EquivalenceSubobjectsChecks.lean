/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46EquivalenceSubobjects

/-! # Independent subobject equivalence checks -/
@[expose] public section
noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [Regular D] [FinitaryExtensive C] [FinitaryExtensive D]
variable (E : C ≌ D)

example (X : C) : Subobject X ≃o Subobject (E.functor.obj X) :=
  EquivalenceSubobjects.orderIso E X

example {X Y : C} (f : X ⟶ Y) (A : Subobject X) :
    FiniteLimitSubobjects.object E.functor ((Subobject.«exists» f).obj A) =
      (Subobject.«exists» (E.functor.map f)).obj (FiniteLimitSubobjects.object E.functor A) :=
  EquivalenceSubobjects.object_exists E f A

example {X : C} {a b : Subobject X} (h : SubobjectInseparable a b) :
    SubobjectInseparable (FiniteLimitSubobjects.object E.functor a)
      (FiniteLimitSubobjects.object E.functor b) := EquivalenceSubobjects.inseparable E h

#print axioms EquivalenceSubobjects.orderIso
#print axioms EquivalenceSubobjects.object_image
#print axioms EquivalenceSubobjects.object_exists
#print axioms EquivalenceSubobjects.inseparable
