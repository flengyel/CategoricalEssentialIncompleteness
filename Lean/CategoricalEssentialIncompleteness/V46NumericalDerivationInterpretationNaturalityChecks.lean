/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationNaturality


/-! # Statement checks in `V46NumericalDerivationInterpretationNaturalityChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
open NumericalPolynomialRepresentation
variable {I : Type} (s : I → PredicateCategory 𝗣𝗔) (t : I → PredicateCategory 𝗧𝗔)
  (c : ∀ i, NumericalPolynomialRepresentation.K.obj (s i) ≅ NumericalPolynomialRepresentation.E.functor.obj (t i))
  {X₀ Y₀ X₁ Y₁ : PredicateCategory 𝗣𝗔} {X₀' Y₀' X₁' Y₁' : PredicateCategory 𝗧𝗔}
  (bX₀ : NumericalPolynomialRepresentation.K.obj X₀ ≅ NumericalPolynomialRepresentation.E.functor.obj X₀')
  (bY₀ : NumericalPolynomialRepresentation.K.obj Y₀ ≅ NumericalPolynomialRepresentation.E.functor.obj Y₀')
  (bX₁ : NumericalPolynomialRepresentation.K.obj X₁ ≅ NumericalPolynomialRepresentation.E.functor.obj X₁')
  (bY₁ : NumericalPolynomialRepresentation.K.obj Y₁ ≅ NumericalPolynomialRepresentation.E.functor.obj Y₁')
  (fX : X₀ ⟶ X₁) (fY : Y₀ ⟶ Y₁) (gX : X₀' ⟶ X₁') (gY : Y₀' ⟶ Y₁')
  (hX : NumericalPolynomialRepresentation.K.map fX ≫ bX₁.hom =
    bX₀.hom ≫ NumericalPolynomialRepresentation.E.functor.map gX)
  (hY : NumericalPolynomialRepresentation.K.map fY ≫ bY₁.hom =
    bY₀.hom ≫ NumericalPolynomialRepresentation.E.functor.map gY)

include hX hY
example (p : SyntaxPolynomial I) :
    NumericalPolynomialRepresentation.K.map ((p.mapCoefficients s).eval.map (fX,fY)) ≫
        (polynomialIso s t c X₁ Y₁ X₁' Y₁' bX₁ bY₁ p).hom =
      (polynomialIso s t c X₀ Y₀ X₀' Y₀' bX₀ bY₀ p).hom ≫
        NumericalPolynomialRepresentation.E.functor.map ((p.mapCoefficients t).eval.map (gX,gY)) := polynomial_natural s t c bX₀ bY₀ bX₁ bY₁ fX fY gX gY hX hY p
example (p : SyntaxPolynomial I)
    (p₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (p₁ : SyntaxPolynomial (PredicateCategory 𝗧𝗔))
    (h₀ : p.mapCoefficients s = p₀) (h₁ : p.mapCoefficients t = p₁) :
    NumericalPolynomialRepresentation.K.map (p₀.eval.map (fX,fY)) ≫
        (normalizedIso s t c X₁ Y₁ X₁' Y₁' bX₁ bY₁ p p₀ p₁ h₀ h₁).hom =
      (normalizedIso s t c X₀ Y₀ X₀' Y₀' bX₀ bY₀ p p₀ p₁ h₀ h₁).hom ≫
        NumericalPolynomialRepresentation.E.functor.map (p₁.eval.map (gX,gY)) :=
  normalized_polynomial_natural s t c bX₀ bY₀ bX₁ bY₁ fX fY gX gY hX hY p p₀ p₁ h₀ h₁
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
