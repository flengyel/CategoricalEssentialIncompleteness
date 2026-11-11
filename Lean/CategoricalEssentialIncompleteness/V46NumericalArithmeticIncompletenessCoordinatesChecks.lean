/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticIncompletenessCoordinates


/-! # Statement checks in `V46NumericalArithmeticIncompletenessCoordinatesChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Incompleteness.Checks
example : ClassicalPrograms.parameterObject ≅
    NumericalTuples.splitComparison.obj NumericalSentenceMorphisms.omega := omegaIso
example : isTotal theta ∧ isTotal nu := ⟨theta_total,nu_total⟩
example (n w : ℕ) : w ∈ ClassicalPrograms.J.map theta.hom n ↔
    w = NamedArithmeticUnarySubstitution.value (M := ℕ) ArithmeticDiagonalCodes.alpha.val n :=
  theta_graph n w
example (n w : ℕ) : w ∈ ClassicalPrograms.J.map nu.hom n ↔
    n ∈ NumericalSentenceMorphisms.sentence.support ∧
      w = NamedArithmeticProofSearch.negationWord ℕ n := nu_graph n w
example : numericalQ.map Coordinates.numericalSyntax.sentenceNegation ≫ syntaxSentenceIso.hom =
    syntaxSentenceIso.hom ≫ nu := syntax_negation_square
example : syntaxTheta ≫ syntaxSentenceIso.hom = theta := syntax_theta_square
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Incompleteness.Checks
