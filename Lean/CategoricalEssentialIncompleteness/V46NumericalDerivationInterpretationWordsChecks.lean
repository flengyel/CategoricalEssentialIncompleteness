/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationWords


/-! # Original PA ordinary-tree words and numerical tree words -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
example (b : Bool) (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    K.obj (Postfix.carrier b p q) ≅ NumericalSyntaxTreeChart.E.functor.obj
      (Postfix.plainCarrier b (p.mapCoefficients labelMap) (q.mapCoefficients labelMap)) := realizedWordIso b p q
example (b : Bool) (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    CarrierScalarIdentity (Postfix.carrier b p q)
      (Postfix.plainCarrier b (p.mapCoefficients labelMap) (q.mapCoefficients labelMap))
      (realizedWordIso b p q) := realizedWordIso_value b p q
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
