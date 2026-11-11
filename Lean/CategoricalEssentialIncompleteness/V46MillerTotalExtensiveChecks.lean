/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTotalExtensive


/-! # Statement checks in `V46MillerTotalExtensiveChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}
example : FinitaryExtensive (TotalCategory P) := inferInstance
example : PreservesColimitsOfShape (Discrete WalkingPair) (underlying (P := P)) := inferInstance
example : PreservesColimit (Functor.empty.{0} (TotalCategory P)) (underlying (P := P)) := inferInstance
example (J : Type*) [Finite J] : PreservesColimitsOfShape (Discrete J) (underlying (P := P)) := inferInstance
example (X Y : TotalCategory P) : IsColimit (BinaryCofan.mk (underlying.map (totalInl X Y)) (underlying.map (totalInr X Y))) :=
  underlyingCoproduct_isColimit X Y
end CategoricalEssentialIncompleteness.V46.Miller.Total
