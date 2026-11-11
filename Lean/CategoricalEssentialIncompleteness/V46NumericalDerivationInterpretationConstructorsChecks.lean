/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationConstructors


/-! # Statement checks in `V46NumericalDerivationInterpretationConstructorsChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
variable {I : Type} (s : I → PredicateCategory 𝗣𝗔) (t : I → PredicateCategory 𝗧𝗔)
  (c : ∀ i, K.obj (s i) ≅ NumericalSyntaxTreeChart.E.functor.obj (t i))
  (a b : SyntaxPolynomial I)
  (p₀ q₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
  (p₁ q₁ : SyntaxPolynomial (PredicateCategory 𝗧𝗔))
  (ha₀ : a.mapCoefficients s = p₀) (hb₀ : b.mapCoefficients s = q₀)
  (ha₁ : a.mapCoefficients t = p₁) (hb₁ : b.mapCoefficients t = q₁)
  (bX : K.obj (termCarrier p₀ q₀) ≅ NumericalSyntaxTreeChart.E.functor.obj (termCarrier p₁ q₁))
  (bY : K.obj (formulaCarrier p₀ q₀) ≅ NumericalSyntaxTreeChart.E.functor.obj (formulaCarrier p₁ q₁))
  (hX : CarrierScalarIdentity (termCarrier p₀ q₀) (termCarrier p₁ q₁) bX)
  (hY : CarrierScalarIdentity (formulaCarrier p₀ q₀) (formulaCarrier p₁ q₁) bY)
  (hC : ∀ i, CarrierScalarIdentity (s i) (t i) (c i))
include hX hY hC ha₀ hb₀ ha₁ hb₁

example :
    K.map (X := p₀.eval.obj (termCarrier p₀ q₀,formulaCarrier p₀ q₀))
      (Y := termCarrier p₀ q₀) (postfixAlgebra 𝗣𝗔 p₀ q₀).str.1 ≫ bX.hom =
      (NumericalPolynomialRepresentation.normalizedIso s t c
        (termCarrier p₀ q₀) (formulaCarrier p₀ q₀) (termCarrier p₁ q₁) (formulaCarrier p₁ q₁)
        bX bY a p₀ p₁ ha₀ ha₁).hom ≫
      NumericalSyntaxTreeChart.E.functor.map
        (X := p₁.eval.obj (termCarrier p₁ q₁,formulaCarrier p₁ q₁))
        (Y := termCarrier p₁ q₁) (postfixAlgebra 𝗧𝗔 p₁ q₁).str.1 :=
  normalized_postfix_term_constructor s t c a b p₀ q₀ p₁ q₁ ha₀ hb₀ ha₁ hb₁ bX bY hX hY hC

example :
    K.map (X := q₀.eval.obj (termCarrier p₀ q₀,formulaCarrier p₀ q₀))
      (Y := formulaCarrier p₀ q₀) (postfixAlgebra 𝗣𝗔 p₀ q₀).str.2 ≫ bY.hom =
      (NumericalPolynomialRepresentation.normalizedIso s t c
        (termCarrier p₀ q₀) (formulaCarrier p₀ q₀) (termCarrier p₁ q₁) (formulaCarrier p₁ q₁)
        bX bY b q₀ q₁ hb₀ hb₁).hom ≫
      NumericalSyntaxTreeChart.E.functor.map
        (X := q₁.eval.obj (termCarrier p₁ q₁,formulaCarrier p₁ q₁))
        (Y := formulaCarrier p₁ q₁) (postfixAlgebra 𝗧𝗔 p₁ q₁).str.2 :=
  normalized_postfix_formula_constructor s t c a b p₀ q₀ p₁ q₁ ha₀ hb₀ ha₁ hb₁ bX bY hX hY hC
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
