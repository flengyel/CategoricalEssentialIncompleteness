import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformInitial

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
variable {P : Uniform.Family} (p q : SyntaxPolynomial (Total.TotalCategory P))

example : IsInitial (wordAlgebra p q) := wordInitial p q
example (R : Total.TotalCategory P) :
    IsInitial (SyntaxPolynomial.algebraWithParameters p q (wordAlgebra p q) R) :=
  wordWithParametersInitial R p q

example (R : Total.TotalCategory P) : parameterWordAlgebra R p q ≅
    SyntaxPolynomial.algebraWithParameters p q (wordAlgebra p q) R :=
  parameterWordAlgebraIso R p q

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
