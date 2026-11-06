import CategoricalEssentialIncompleteness.V46ArithmeticNamedAxiomComparisonEquality
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparisonEqualityChecks
open ArithmeticNamedAxiomComparison NamedArithmeticSignature

example (A : SyntacticPredicates.Carrier) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] (Theory.Eq.refl ℒₒᵣ)) :=
  eqRefl_admissible A

example (A : SyntacticPredicates.Carrier) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] (Theory.Eq.symm ℒₒᵣ)) :=
  eqSymm_admissible A

example (A : SyntacticPredicates.Carrier) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] (Theory.Eq.trans ℒₒᵣ)) :=
  eqTrans_admissible A

example (A : SyntacticPredicates.Carrier) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] (Theory.Eq.funcExt .add)) :=
  eqAddExt_admissible A

example (A : SyntacticPredicates.Carrier) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] (Theory.Eq.funcExt .mul)) :=
  eqMulExt_admissible A

example (A : SyntacticPredicates.Carrier) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] (Theory.Eq.relExt .eq)) :=
  eqEqRelExt_admissible A

example (A : SyntacticPredicates.Carrier) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] (Theory.Eq.relExt .lt)) :=
  eqLtRelExt_admissible A

example (A : SyntacticPredicates.Carrier) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] (Theory.Eq.funcExt .zero)) :=
  eqZeroExt_admissible A

example (A : SyntacticPredicates.Carrier) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] (Theory.Eq.funcExt .one)) :=
  eqOneExt_admissible A

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparisonEqualityChecks
