/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedProofTranslation


/-! # Translation of finite LK2 proofs to named proofs -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedProofTranslationChecks
open NamedArithmeticSignature ArithmeticNamedProofTranslation

example (A : SyntacticPredicates.Carrier) (T : Theory ℒₒᵣ)
    (hA : ∀ ψ ∈ T, SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] ψ))
    (φ : ArithmeticSentence) (h : T ⊢ φ) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] φ) :=
  sentence A T hA φ h


example (φ : ArithmeticSemisentence 1) (n : ℕ) :
    (ArithmeticNamedTranslation.translateFormula 1 ![0] φ).substitute 0
      (NamedArithmeticSignature.numeral n) =
        some (ArithmeticNamedTranslation.translateFormula 1 ![]
          (φ/[ArithmeticNamedProofNumerals.expandedNumeral n] : ArithmeticSentence)) :=
  expanded_instance_substitution φ n

example (A : SyntacticPredicates.Carrier)
    (hPA : ∀ ψ ∈ 𝗣𝗔, SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] ψ))
    (φ : ArithmeticSemisentence 1) (n : ℕ)
    (h : 𝗣𝗔 ⊢ (φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 1 ![]
        (φ/[ArithmeticNamedProofNumerals.expandedNumeral n] : ArithmeticSentence)) :=
  expanded_instance_proof A hPA φ n h

example (A : SyntacticPredicates.Carrier)
    (hPA : ∀ ψ ∈ 𝗣𝗔, SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] ψ))
    (φ : ArithmeticSemisentence 1) (n : ℕ)
    (h : 𝗣𝗔 ⊢ ∼(φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) :
    SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (.neg (ArithmeticNamedTranslation.translateFormula 1 ![]
        (φ/[ArithmeticNamedProofNumerals.expandedNumeral n] : ArithmeticSentence))) :=
  expanded_instance_refutation A hPA φ n h

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedProofTranslationChecks
