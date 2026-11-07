import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationStandardCoherence

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.StandardCoherenceChecks
open SyntacticSyntax SyntacticDerivation StandardCoherence WordCoherence

example {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)
    (X : PredicateCategory 𝗣𝗔) :
    K.map ((PolynomialComparison.comparison R).hom.app X) ≫ (ordinaryObjectIso R X).hom =
      (oneSortInputIsoTo (PolynomialComparison.coefficients R)
        (PolynomialComparison.coefficients (interpretedRules R)) N
        (interpreted_constructor_polynomial R) X).hom ≫
        (PolynomialComparison.comparison (interpretedRules R)).hom.app (K.obj X) :=
  standardcomparison_square R X

example {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)
    (B : Endofunctor.Algebra (PolynomialComparison.nested (PolynomialComparison.coefficients R) N)) :
    mappedOrdinaryAlgebra R (PolynomialComparison.mappedAlgebra R B) ≅
      PolynomialComparison.mappedAlgebra (interpretedRules R)
        (mappedOneSortAlgebraTo (PolynomialComparison.coefficients R)
          (PolynomialComparison.coefficients (interpretedRules R)) N
          (interpreted_constructor_polynomial R) B) := mappedAlgebraIso R B

example {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)
    (B : Endofunctor.Algebra (PolynomialComparison.nested (PolynomialComparison.coefficients R) N)) :
    (mappedAlgebraIso R B).hom.f = 𝟙 (K.obj B.a) := mappedAlgebraIso_hom_f R B

example {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)
    (X : NumericalTuples.Object) :
    (Coherence.targetComparison R).hom.app X =
      (actualNestedChange R X).hom ≫ (PolynomialComparison.comparison (interpretedRules R)).hom.app X :=
  targetComparison_eq R X

end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.StandardCoherenceChecks
