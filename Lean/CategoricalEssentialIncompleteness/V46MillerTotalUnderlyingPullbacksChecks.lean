/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTotalUnderlyingPullbacks


/-! # Statement checks in `V46MillerTotalUnderlyingPullbacksChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}
example : PreservesLimitsOfShape WalkingCospan (underlying (P := P)) := inferInstance
example {W X Y Z : TotalCategory P} {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback p q f g) : IsPullback (underlying.map p) (underlying.map q) (underlying.map f) (underlying.map g) :=
  underlying_isPullback h
end CategoricalEssentialIncompleteness.V46.Miller.Total
