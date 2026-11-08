import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformParameterAlgebra

noncomputable section
open CategoryTheory
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
variable {P : Uniform.Family} (R : Total.TotalCategory P)
  (p q : SyntaxPolynomial (Total.TotalCategory P))

example : Endofunctor.Algebra
    (SyntaxPolynomial.jointFunctor (p.withParameters R) (q.withParameters R)) :=
  parameterWordAlgebra R p q

example (formula : Bool) (r u value : ℕ) :
    value ∈ Total.val (parameterConstructor R p q formula).left.hom (Nat.pair r u) ↔
      fiber R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
        (if formula then q else p) (r,u) ∧
      value = Nat.pair r (SyntacticSyntax.Coding.constructor formula
        (skeleton (if formula then q else p))
        (constantUnlift (if formula then q else p) u)) :=
  parameterConstructor_graph R p q formula r u value

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
