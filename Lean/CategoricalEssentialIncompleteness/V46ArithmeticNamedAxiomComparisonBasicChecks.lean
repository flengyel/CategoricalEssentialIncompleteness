/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedAxiomComparisonBasic


/-! # Statement checks in `V46ArithmeticNamedAxiomComparisonBasicChecks` -/

@[expose] public section
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
