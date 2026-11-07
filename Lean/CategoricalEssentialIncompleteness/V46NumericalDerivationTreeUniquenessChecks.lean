import CategoricalEssentialIncompleteness.V46NumericalDerivationTreeUniqueness
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
