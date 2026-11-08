import CategoricalEssentialIncompleteness.V46MillerSyntaxRawConstantComparison
noncomputable section
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
variable {P : Uniform.Family} (R A B : Total.TotalCategory P)
example (p : SyntaxPolynomial (Total.TotalCategory P)) :
    Syntax.Raw.constantPolynomialLeft R A B p=Syntax.Raw.constantPolynomialRight R A B p :=
  Syntax.Raw.constantPolynomialSquare R A B p
example (p : SyntaxPolynomial (Total.TotalCategory P)) :
    (Syntax.Raw.liftIso R A B p).hom ≫
      Syntax.Raw.rawAction R (Syntax.Raw.constantObject R A) (Syntax.Raw.constantObject R B)
        (constantFamily R A) (constantFamily R B)
        (Syntax.Raw.explicitFamilyIso R A).hom (Syntax.Raw.explicitFamilyIso R B).hom p ≫
      (Syntax.Raw.comparison R (constantFamily R A) (constantFamily R B) p).hom ≫
      SyntaxPolynomial.parameterComparison R (A,B) p=
        (Syntax.Raw.explicitFamilyIso R (Syntax.Raw.baseObject A B p)).hom ≫
          (constantFamilyFunctor R).map (Syntax.Raw.baseComparison A B p).hom :=
  Syntax.Raw.constantPolynomialSquare R A B p
