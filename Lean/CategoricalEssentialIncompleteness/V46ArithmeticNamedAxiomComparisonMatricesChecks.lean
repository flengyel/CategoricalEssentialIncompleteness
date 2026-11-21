/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedAxiomComparisonMatrices


/-! # Direct comparison of the arithmetic/order axiom matrices -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparisonMatricesChecks
open ArithmeticNamedAxiomComparison NamedArithmeticSignature

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.addZero) :=
  addZero_admissible A hΓ

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.addAssoc) :=
  addAssoc_admissible A hΓ

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.addComm) :=
  addComm_admissible A hΓ

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.addEqOfLt) :=
  addEqOfLt_admissible A hΓ

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.zeroLe) :=
  zeroLe_admissible A hΓ

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.zeroLtOne) :=
  zeroLtOne_admissible A hΓ

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.oneLeOfZeroLt) :=
  oneLeOfZeroLt_admissible A hΓ

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.addLtAdd) :=
  addLtAdd_admissible A hΓ

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.mulZero) :=
  mulZero_admissible A hΓ

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.mulOne) :=
  mulOne_admissible A hΓ

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.mulAssoc) :=
  mulAssoc_admissible A hΓ

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.mulComm) :=
  mulComm_admissible A hΓ

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.mulLtMul) :=
  mulLtMul_admissible A hΓ

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.distr) :=
  distr_admissible A hΓ

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.ltIrrefl) :=
  ltIrrefl_admissible A hΓ

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.ltTrans) :=
  ltTrans_admissible A hΓ

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] PeanoMinus.Axiom.ltTri) :=
  ltTri_admissible A hΓ

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparisonMatricesChecks
