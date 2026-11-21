/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformInitialExplicit


/-! # The universal property on the original explicit parameter-word families -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
variable {P : Uniform.Family} (R : Total.TotalCategory P) (p q : SyntaxPolynomial (Total.TotalCategory P))

example : IsInitial (parameterWordAlgebra R p q) := explicitWordInitial R p q

example (B : Endofunctor.Algebra
    (SyntaxPolynomial.jointFunctor (p.withParameters R) (q.withParameters R)))
    (f : parameterWordAlgebra R p q ⟶ B) : f=parameterFoldHom B :=
  parameterFoldHom_unique B f

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
