/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTotalUnderlying


/-! # Statement checks in `V46MillerTotalUnderlyingChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}
example : (underlying (P := P)).ReflectsIsomorphisms := inferInstance
example : PreservesLimits (underlying (P := P)) := inferInstance
example {X Y : TotalCategory P} (f : X ⟶ Y) (x : {n // n ∈ X.obj.support}) :
    (underlying.map f x).val ∈ val f.hom x.val := totalFunction_mem f x
example {X Y : TotalCategory P} (f : X ⟶ Y) (x : {n // n ∈ X.obj.support}) (y : {n // n ∈ Y.obj.support}) :
    underlying.map f x = y ↔ y.val ∈ val f.hom x.val := totalFunction_eq_iff f x y
end CategoricalEssentialIncompleteness.V46.Miller.Total
