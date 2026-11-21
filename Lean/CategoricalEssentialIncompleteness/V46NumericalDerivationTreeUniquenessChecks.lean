/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationTreeUniqueness


/-! # Uniqueness of folds retaining the underlying derivation tree -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open SyntacticDerivation

example {F : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N)
    (B : Endofunctor.Algebra (PolynomialComparison.ordinary R))
    (f g : (NumericalDerivation.codeAlgebra R).a.left ⟶ B.a)
    (hf : (NumericalDerivation.codeAlgebra R).str.left ≫ f =
      InputGeometry.forget R (NumericalDerivation.codeAlgebra R).a ≫
        (PolynomialComparison.ordinary R).map f ≫ B.str)
    (hg : (NumericalDerivation.codeAlgebra R).str.left ≫ g =
      InputGeometry.forget R (NumericalDerivation.codeAlgebra R).a ≫
        (PolynomialComparison.ordinary R).map g ≫ B.str) : f = g :=
  NumericalDerivation.tree_map_unique R B f g hf hg
