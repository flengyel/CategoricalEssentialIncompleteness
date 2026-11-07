import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationWordCoherence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.WordCoherence
open SyntacticSyntax SyntacticDerivation
example {I : Type} (g : I → NumericalTuples.Object) (p : SyntaxPolynomial I)
    (A : PredicateCategory 𝗧𝗔 × PredicateCategory 𝗧𝗔) :
    (componentNormalized E.inverse.obj id (fun X => E.counitIso.app X)
      (p.mapCoefficients g) (p.mapCoefficients (fun i => E.inverse.obj (g i))) (p.mapCoefficients g)
      (mapCoefficients_comp g E.inverse.obj p) (mapCoefficients_id (p.mapCoefficients g)) A).hom =
    (SyntaxPolynomialTransport.component E (fun i => E.inverse.obj (g i)) g
      (fun i => E.counitIso.app (g i)) p A).hom := coefficient_reindex g p A
variable {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)
example : (SyntaxPolynomial.constructors (PolynomialComparison.coefficients R) N).mapCoefficients K.obj =
    SyntaxPolynomial.constructors (PolynomialComparison.coefficients (interpretedRules R)) N :=
  interpreted_constructor_polynomial R
example (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    (SyntaxPolynomial.constructors (PolynomialComparison.coefficients R) N) .unit)) :
    K.map (constructorProjection (PolynomialComparison.coefficients R) N A) ≫
      (oneSortInputIsoTo (PolynomialComparison.coefficients R)
        (PolynomialComparison.coefficients (interpretedRules R)) N (interpreted_constructor_polynomial R) A.a.1).hom =
      (constructorInputIsoTo (PolynomialComparison.coefficients R)
        (PolynomialComparison.coefficients (interpretedRules R)) N (interpreted_constructor_polynomial R) A.a).hom ≫
      constructorProjection (PolynomialComparison.coefficients (interpretedRules R)) N
        (mappedJointAlgebraTo (PolynomialComparison.coefficients R)
          (PolynomialComparison.coefficients (interpretedRules R)) N (interpreted_constructor_polynomial R) A) :=
  projection_squareTo _ _ _ _ A
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.WordCoherence
