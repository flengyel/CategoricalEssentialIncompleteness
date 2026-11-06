import CategoricalEssentialIncompleteness.V46ArithmeticNamedAxiomComparisonInduction

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparisonInductionChecks
open ArithmeticNamedAxiomComparison NamedArithmeticSignature ArithmeticNamedOpenTranslation

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A)
    (φ : ArithmeticSemiformula ℕ 1) (x : ℕ) (fn : ℕ → ℕ) (hf : ∀ i, fn i < x) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (formula x ![] fn (succInd φ)) :=
  succInd_admissible A hΓ φ x fn hf

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A)
    (φ : ArithmeticSemiformula ℕ 1) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] (.univCl (succInd φ))) :=
  induction_admissible A hΓ φ

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparisonInductionChecks
