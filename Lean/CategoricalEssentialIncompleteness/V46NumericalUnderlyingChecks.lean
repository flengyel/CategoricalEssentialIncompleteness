/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalUnderlying


/-! # Statement checks in `V46NumericalUnderlyingChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46

example : NumericalTuples.Object ⥤ Type := NumericalUnderlying.functor
example : PreservesFiniteLimits NumericalUnderlying.functor := inferInstance
example : ReflectsFiniteLimits NumericalUnderlying.functor := inferInstance
example : NumericalUnderlying.functor.ReflectsIsomorphisms := inferInstance
example : PreservesColimitsOfShape (Discrete WalkingPair) NumericalUnderlying.functor := inferInstance

example (C D E : NumericalTuples.Object) (f : C ⟶ E) (g : D ⟶ E) :
    PreservesLimit (cospan f g) NumericalUnderlying.functor := inferInstance

example (C : NumericalTuples.Object) :
    NumericalTuples.Point C ≃ (NumericalTuples.terminalObject ⟶ C) :=
  NumericalUnderlying.pointHomEquiv C
