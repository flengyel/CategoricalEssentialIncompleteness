/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawComparison


/-! # Raw-fiber comparison for every parameter slice -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw.Checks
noncomputable section
example {P : Uniform.Family} (R : Total.TotalCategory P) (X Y : Over R)
    (p : SyntaxPolynomial (Total.TotalCategory P)) :
    object R X Y p ≅ (p.withParameters R).eval.obj (X,Y) := comparison R X Y p
example {P : Uniform.Family} (R : Total.TotalCategory P) (p : SyntaxPolynomial (Total.TotalCategory P)) :
    expressionFunctor R p ≅ (p.withParameters R).eval := comparisonIso R p
end
end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw.Checks
