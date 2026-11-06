import CategoricalEssentialIncompleteness.V46ArithmeticNamedAxiomComparisonBasic

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparisonBasicChecks
open ArithmeticNamedAxiomComparison NamedArithmeticSignature

example (A : SyntacticPredicates.Carrier) :
    ExtendsPA A ↔ ∀ φ, PASeed φ → SyntacticNamedHilbert.Derives
      functionSymbols relationSymbols bound A (canonicalClosure φ) :=
  extendsPA_iff_canonical A

example (φ : NamedArithmeticSignature.Formula) :
    (canonicalClosure φ).freeVariables = [] :=
  canonicalClosure_sentence φ

example (A : SyntacticPredicates.Carrier) (names : List ℕ) (φ : NamedArithmeticSignature.Formula)
    (h : SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A (closure names φ)) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A φ :=
  derives_of_closure A names φ h

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparisonBasicChecks
