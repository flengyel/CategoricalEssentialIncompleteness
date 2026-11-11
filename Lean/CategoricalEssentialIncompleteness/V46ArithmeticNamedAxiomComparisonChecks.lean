/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedAxiomComparison


/-! # Statement checks in `V46ArithmeticNamedAxiomComparisonChecks` -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparisonChecks
open NamedArithmeticSignature ArithmeticNamedAxiomComparison

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A)
    (φ : ArithmeticSentence) (hφ : φ ∈ 𝗣𝗔) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] φ) :=
  axiomsAdmissible_PA A hΓ φ hφ

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A) :
    ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔 :=
  axiomsAdmissible_of_extendsPA A hΓ

example (A : SyntacticPredicates.Carrier)
    (hΓ : ∀ ψ : NamedArithmeticSignature.Formula,
      ψ.freeVariables = [] →
      (∃ θ, PASeed θ ∧ UniversalClosure θ ψ) →
      SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A ψ)
    (φ : ArithmeticSentence) (hφ : φ ∈ 𝗣𝗔) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] φ) :=
  axiomsAdmissible_PA A (fun ψ hψ => hΓ ψ hψ.1 hψ.2) φ hφ

example (A : SyntacticPredicates.Carrier) (hΓ : ExtendsPA A)
    (φ : ArithmeticSentence) (hφ : 𝗣𝗔 ⊢ φ) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] φ) :=
  sentence_PA_of_extendsPA A hΓ φ hφ

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparisonChecks
