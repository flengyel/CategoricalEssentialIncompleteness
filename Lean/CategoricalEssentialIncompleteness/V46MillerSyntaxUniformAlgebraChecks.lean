import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformAlgebra
open CategoryTheory
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw.Checks
noncomputable section
example {P : Uniform.Family} (p q : SyntaxPolynomial (Total.TotalCategory P)) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q) := wordAlgebra p q
example {P : Uniform.Family} (p q : SyntaxPolynomial (Total.TotalCategory P)) :
    (baseComparison (wordObject false p q) (wordObject true p q) p).hom ≫ (wordAlgebra p q).str.1=
      rawWordConstructor p q false := wordAlgebra_term_constructor p q
example {P : Uniform.Family} (p q : SyntaxPolynomial (Total.TotalCategory P)) :
    (baseComparison (wordObject false p q) (wordObject true p q) q).hom ≫ (wordAlgebra p q).str.2=
      rawWordConstructor p q true := wordAlgebra_formula_constructor p q
end
end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw.Checks
