/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationPlain


/-! # Full stored/plain constructor comparison -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
open SyntacticLists
example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    (b : Bool) (p q : RawPolynomial) (x : Obj T M (Postfix.carrier b p q)) :
    ((F T M).map (Postfix.plainCarrierIso T b p q).hom x).val = x.val := toPlain_value T M b p q x
example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    (b : Bool) (p q : RawPolynomial) (x : Obj T M (Postfix.plainCarrier b p q)) :
    ((F T M).map (Postfix.plainCarrierIso T b p q).inv x).val = x.val := fromPlain_value T M b p q x

variable {I : Type} (s : I → PredicateCategory 𝗣𝗔) (t : I → PredicateCategory 𝗧𝗔)
  (c : ∀ i, K.obj (s i) ≅ NumericalSyntaxTreeChart.E.functor.obj (t i))
  (a b : SyntaxPolynomial I)
  (p₀ q₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
  (p₁ q₁ : SyntaxPolynomial (PredicateCategory 𝗧𝗔))
  (ha₀ : a.mapCoefficients s = p₀) (hb₀ : b.mapCoefficients s = q₀)
  (ha₁ : a.mapCoefficients t = p₁) (hb₁ : b.mapCoefficients t = q₁)
  (bX : K.obj (Postfix.plainCarrier false p₀ q₀) ≅
    NumericalSyntaxTreeChart.E.functor.obj (Postfix.plainCarrier false p₁ q₁))
  (bY : K.obj (Postfix.plainCarrier true p₀ q₀) ≅
    NumericalSyntaxTreeChart.E.functor.obj (Postfix.plainCarrier true p₁ q₁))
  (hX : CarrierScalarIdentity (Postfix.plainCarrier false p₀ q₀) (Postfix.plainCarrier false p₁ q₁) bX)
  (hY : CarrierScalarIdentity (Postfix.plainCarrier true p₀ q₀) (Postfix.plainCarrier true p₁ q₁) bY)
  (hC : ∀ i, CarrierScalarIdentity (s i) (t i) (c i))
include hX hY hC ha₀ hb₀ ha₁ hb₁

example :
    K.map (X := p₀.eval.obj (Postfix.plainCarrier false p₀ q₀,Postfix.plainCarrier true p₀ q₀))
      (Y := Postfix.plainCarrier false p₀ q₀) (plainPostfixAlgebra 𝗣𝗔 p₀ q₀).str.1 ≫ bX.hom =
      (NumericalPolynomialRepresentation.normalizedIso s t c
        (Postfix.plainCarrier false p₀ q₀) (Postfix.plainCarrier true p₀ q₀)
        (Postfix.plainCarrier false p₁ q₁) (Postfix.plainCarrier true p₁ q₁)
        bX bY a p₀ p₁ ha₀ ha₁).hom ≫
      NumericalSyntaxTreeChart.E.functor.map
        (X := p₁.eval.obj (Postfix.plainCarrier false p₁ q₁,Postfix.plainCarrier true p₁ q₁))
        (Y := Postfix.plainCarrier false p₁ q₁) (plainPostfixAlgebra 𝗧𝗔 p₁ q₁).str.1 :=
  normalized_plain_term_constructor s t c a b p₀ q₀ p₁ q₁ ha₀ hb₀ ha₁ hb₁ bX bY hX hY hC

example :
    K.map (X := q₀.eval.obj (Postfix.plainCarrier false p₀ q₀,Postfix.plainCarrier true p₀ q₀))
      (Y := Postfix.plainCarrier true p₀ q₀) (plainPostfixAlgebra 𝗣𝗔 p₀ q₀).str.2 ≫ bY.hom =
      (NumericalPolynomialRepresentation.normalizedIso s t c
        (Postfix.plainCarrier false p₀ q₀) (Postfix.plainCarrier true p₀ q₀)
        (Postfix.plainCarrier false p₁ q₁) (Postfix.plainCarrier true p₁ q₁)
        bX bY b q₀ q₁ hb₀ hb₁).hom ≫
      NumericalSyntaxTreeChart.E.functor.map
        (X := q₁.eval.obj (Postfix.plainCarrier false p₁ q₁,Postfix.plainCarrier true p₁ q₁))
        (Y := Postfix.plainCarrier true p₁ q₁) (plainPostfixAlgebra 𝗧𝗔 p₁ q₁).str.2 :=
  normalized_plain_formula_constructor s t c a b p₀ q₀ p₁ q₁ ha₀ hb₀ ha₁ hb₁ bX bY hX hY hC

omit hX hY
variable (jX : K.obj (Postfix.carrier false p₀ q₀) ≅
    NumericalSyntaxTreeChart.E.functor.obj (Postfix.plainCarrier false p₁ q₁))
  (jY : K.obj (Postfix.carrier true p₀ q₀) ≅
    NumericalSyntaxTreeChart.E.functor.obj (Postfix.plainCarrier true p₁ q₁))
  (hjX : CarrierScalarIdentity (Postfix.carrier false p₀ q₀) (Postfix.plainCarrier false p₁ q₁) jX)
  (hjY : CarrierScalarIdentity (Postfix.carrier true p₀ q₀) (Postfix.plainCarrier true p₁ q₁) jY)
include hjX hjY

example :
    K.map (X := p₀.eval.obj (Postfix.carrier false p₀ q₀,Postfix.carrier true p₀ q₀))
      (Y := Postfix.carrier false p₀ q₀) (postfixAlgebra 𝗣𝗔 p₀ q₀).str.1 ≫ jX.hom =
      (NumericalPolynomialRepresentation.normalizedIso s t c
        (Postfix.carrier false p₀ q₀) (Postfix.carrier true p₀ q₀)
        (Postfix.plainCarrier false p₁ q₁) (Postfix.plainCarrier true p₁ q₁)
        jX jY a p₀ p₁ ha₀ ha₁).hom ≫
      NumericalSyntaxTreeChart.E.functor.map
        (X := p₁.eval.obj (Postfix.plainCarrier false p₁ q₁,Postfix.plainCarrier true p₁ q₁))
        (Y := Postfix.plainCarrier false p₁ q₁) (plainPostfixAlgebra 𝗧𝗔 p₁ q₁).str.1 :=
  normalized_mixed_term_constructor s t c a b p₀ q₀ p₁ q₁ ha₀ hb₀ ha₁ hb₁ jX jY hjX hjY hC

example :
    K.map (X := q₀.eval.obj (Postfix.carrier false p₀ q₀,Postfix.carrier true p₀ q₀))
      (Y := Postfix.carrier true p₀ q₀) (postfixAlgebra 𝗣𝗔 p₀ q₀).str.2 ≫ jY.hom =
      (NumericalPolynomialRepresentation.normalizedIso s t c
        (Postfix.carrier false p₀ q₀) (Postfix.carrier true p₀ q₀)
        (Postfix.plainCarrier false p₁ q₁) (Postfix.plainCarrier true p₁ q₁)
        jX jY b q₀ q₁ hb₀ hb₁).hom ≫
      NumericalSyntaxTreeChart.E.functor.map
        (X := q₁.eval.obj (Postfix.plainCarrier false p₁ q₁,Postfix.plainCarrier true p₁ q₁))
        (Y := Postfix.plainCarrier true p₁ q₁) (plainPostfixAlgebra 𝗧𝗔 p₁ q₁).str.2 :=
  normalized_mixed_formula_constructor s t c a b p₀ q₀ p₁ q₁ ha₀ hb₀ ha₁ hb₁ jX jY hjX hjY hC
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
