import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationPolynomial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.Polynomial
variable {I : Type} (s : I → PredicateCategory 𝗣𝗔) (t : I → PredicateCategory 𝗧𝗔)
  (c : ∀ i, K.obj (s i) ≅ NumericalSyntaxTreeChart.E.functor.obj (t i))
  (X Y : PredicateCategory 𝗣𝗔) (X' Y' : PredicateCategory 𝗧𝗔)
  (bX : K.obj X ≅ NumericalSyntaxTreeChart.E.functor.obj X')
  (bY : K.obj Y ≅ NumericalSyntaxTreeChart.E.functor.obj Y')
example (p : SyntaxPolynomial I) {A B : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔} (f : A ⟶ B) :
    K.map ((p.mapCoefficients s).eval.map f) ≫ (component s p B).hom =
      (component s p A).hom ≫
        (p.mapCoefficients (fun i => K.obj (s i))).eval.map ((K.prod K).map f) :=
  component_natural s p f
example (p : SyntaxPolynomial I) :
    (component s p (X,Y)).hom ≫
      (p.mapCoefficients (fun i => K.obj (s i))).eval.map (leafMap bX bY) ≫
        (SyntaxPolynomialTransport.component NumericalSyntaxTreeChart.E t (fun i => K.obj (s i))
          (fun i => (c i).symm) p (X',Y')).inv =
      (NumericalPolynomialRepresentation.polynomialIso s t c X Y X' Y' bX bY p).hom :=
  component_factorization s t c X Y X' Y' bX bY p
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.Polynomial
