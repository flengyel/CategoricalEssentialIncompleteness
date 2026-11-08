import CategoricalEssentialIncompleteness.V46MillerSyntaxComparison
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Checks
example (P : Uniform.Family) : PreservesFiniteLimits (predicateFunctor P) := inferInstance
example (P : Uniform.Family) : PreservesFiniteCoproducts (predicateFunctor P) := inferInstance
example (P : Uniform.Family) (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    p.eval ⋙ predicateFunctor P ≅
      ((predicateFunctor P).prod (predicateFunctor P)) ⋙ (Polynomial.mapped P p).eval :=
  Polynomial.naturalIso P p
noncomputable example (P : Uniform.Family) (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (Polynomial.mapped P p) (Polynomial.mapped P q)) :=
  Polynomial.wordAlgebra P p q
end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Checks
