/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationIndexAlgebra


/-! # Statement checks in `V46NumericalDerivationInterpretationIndexAlgebraChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.IndexAlgebraChecks
open SyntacticSyntax IndexAlgebra
local notation "E" => NumericalSyntaxTreeChart.E
local notation "c" => fun C : PredicateCategory 𝗣𝗔 => Iso.symm (NumericalSyntaxTreeChart.E.counitIso.app (K.obj C))

private def wordScalar (C : PredicateCategory 𝗧𝗔)
    (x : NumericalTuples.Point ((E).functor.obj C)) : ℕ :=
  ((NumericalSyntaxTreeChart.wordPresentationIso C).hom.toFun x).val

example (C : PredicateCategory 𝗧𝗔) (x : NumericalTuples.Point ((E).functor.obj C)) :
    wordScalar C x = ((NumericalSyntaxTreeChart.wordPresentationIso C).hom.toFun x).val := rfl

example (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    NumericalSyntaxTreeChart.normalizedPair (p.mapCoefficients K.obj) (q.mapCoefficients K.obj) ≅
      Initial.mappedLiteralPair id labelMap c p q (p.mapCoefficients labelMap)
        (q.mapCoefficients labelMap) (p.mapCoefficients K.obj) (q.mapCoefficients K.obj) rfl rfl rfl rfl
        (plainPostfixAlgebra 𝗧𝗔 (p.mapCoefficients labelMap) (q.mapCoefficients labelMap)) :=
  normalizedTemplateIso p q

example (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (pN qN : SyntaxPolynomial NumericalTuples.Object)
    (hp : p.mapCoefficients K.obj = pN) (hq : q.mapCoefficients K.obj = qN) :
    NumericalSyntaxTreeChart.normalizedPair pN qN ≅
      Initial.mappedLiteralPair id labelMap c p q (p.mapCoefficients labelMap)
        (q.mapCoefficients labelMap) pN qN rfl rfl hp hq
        (plainPostfixAlgebra 𝗧𝗔 (p.mapCoefficients labelMap) (q.mapCoefficients labelMap)) :=
  normalizedTemplateIsoTo p q pN qN hp hq

example (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (pN qN : SyntaxPolynomial NumericalTuples.Object)
    (hp : p.mapCoefficients K.obj = pN) (hq : q.mapCoefficients K.obj = qN) :
    let C : PredicateCategory 𝗧𝗔 := Postfix.plainCarrier false
      ((pN).mapCoefficients (E).inverse.obj) ((qN).mapCoefficients (E).inverse.obj)
    let D : PredicateCategory 𝗧𝗔 := Postfix.plainCarrier false
      (p.mapCoefficients labelMap) (q.mapCoefficients labelMap)
    let f : (E).functor.obj C ⟶ (E).functor.obj D :=
      (normalizedTemplateIsoTo p q pN qN hp hq).hom.f.1
    ∀ x : NumericalTuples.Point ((E).functor.obj C),
      wordScalar D (f.toFun x) = wordScalar C x := by
  intro C D f x
  exact normalizedTemplateIsoTo_word p q pN qN hp hq x

example (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (pN qN : SyntaxPolynomial NumericalTuples.Object)
    (hp : p.mapCoefficients K.obj = pN) (hq : q.mapCoefficients K.obj = qN) :
    let C : PredicateCategory 𝗧𝗔 := Postfix.plainCarrier false
      (p.mapCoefficients labelMap) (q.mapCoefficients labelMap)
    let D : PredicateCategory 𝗧𝗔 := Postfix.plainCarrier false
      ((pN).mapCoefficients (E).inverse.obj) ((qN).mapCoefficients (E).inverse.obj)
    let f : (E).functor.obj C ⟶ (E).functor.obj D :=
      (normalizedTemplateIsoTo p q pN qN hp hq).inv.f.1
    ∀ x : NumericalTuples.Point ((E).functor.obj C),
      wordScalar D (f.toFun x) = wordScalar C x := by
  intro C D f x
  exact normalizedTemplateIsoTo_inverse_word p q pN qN hp hq x

end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.IndexAlgebraChecks
