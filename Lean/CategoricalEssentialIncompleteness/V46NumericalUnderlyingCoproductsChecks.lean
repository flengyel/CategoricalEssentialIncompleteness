/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalUnderlyingCoproducts


/-! # Statement checks in `V46NumericalUnderlyingCoproductsChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46

example : PreservesColimit (Functor.empty.{0} NumericalTuples.Object) NumericalUnderlying.functor :=
  inferInstance

example (n : ℕ) : PreservesColimitsOfShape (Discrete (Fin n)) NumericalUnderlying.functor :=
  inferInstance

example : IsEmpty (NumericalTuples.Point (⊥_ NumericalTuples.Object)) := inferInstance
