/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawLeaves


/-! # Statement checks in `V46MillerSyntaxRawLeavesChecks` -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw.Checks
noncomputable section
example {P : Uniform.Family} (R : Total.TotalCategory P) (X Y : Over R) : object R X Y .term ≅ X := termIso R X Y
example {P : Uniform.Family} (R : Total.TotalCategory P) (X Y : Over R) : object R X Y .formula ≅ Y := formulaIso R X Y
example {P : Uniform.Family} (R : Total.TotalCategory P) (X Y : Over R) (C : Total.TotalCategory P) :
    object R X Y (.coefficient C) ≅ constantFamily R C := coefficientIso R X Y C
example {P : Uniform.Family} (R : Total.TotalCategory P) (X Y : Over R) : object R X Y .unit ≅ ⊤_ (Over R) := unitIso R X Y
end
end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw.Checks
