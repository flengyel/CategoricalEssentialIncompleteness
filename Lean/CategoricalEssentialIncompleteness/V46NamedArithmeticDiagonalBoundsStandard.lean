/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodes
public import CategoricalEssentialIncompleteness.V46ArithmeticNamedProofTranslation
public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbertRealization
public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbertRefutations
public import CategoricalEssentialIncompleteness.V46NamedArithmeticFixedStandard
public import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchDiagonal
public import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchNegation

/-! # Standard proof witnesses for the actual arithmetic diagonal predicates

The intermediate premise concerns individual PA axioms in the literal
named calculus. The printed Γ-extension premise is discharged separately
by the concrete arithmetic-axiom comparison before the final application.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds

open NamedArithmeticSignature

/-- The named output has the expanded source numeral and the same binder
seed as the actual successful named substitution. -/
def instanceFormula (φ : ArithmeticSemisentence 1) (n : ℕ) : Formula :=
  ArithmeticNamedTranslation.translateFormula 1 ![]
    (φ/[ArithmeticNamedProofNumerals.expandedNumeral n] : ArithmeticSentence)

theorem standard_instance_result (φ : ArithmeticSemisentence 1) (n : ℕ) :
    NamedArithmeticUnarySubstitution.value φ n =
        NamedArithmeticSignature.formulaCode (instanceFormula φ n) ∧
      (instanceFormula φ n).freeVariables = [] := by
  obtain ⟨out,hsub,hvalue,hclosed⟩ := NamedArithmeticFixedSubstitution.standard_literal_result
    (NamedArithmeticUnarySubstitution.namedFormula φ)
    (NamedArithmeticUnarySubstitution.namedFormula_freeVariables φ) n
  have hresult := ArithmeticNamedProofTranslation.expanded_instance_substitution φ n
  have hout : out = instanceFormula φ n := Option.some.inj (hsub.symm.trans hresult)
  subst out
  exact ⟨hvalue,hclosed⟩

/-- An individual source PA proof is realized in the selected program of
the actual generated Γ proof object, at the actual computed sentence word. -/
theorem instance_theorem_of_axioms_admissible (A : Carrier)
    (hPA : ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔)
    (φ : ArithmeticSemisentence 1) (n : ℕ)
    (h : 𝗣𝗔 ⊢ (φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) :
    (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
      variableSymbols functionSymbols relationSymbols bound A).val.Evalb
        ![NamedArithmeticUnarySubstitution.value φ n] := by
  have hp := ArithmeticNamedProofTranslation.expanded_instance_proof A hPA φ n h
  have hresult := standard_instance_result φ n
  have hm := SyntacticNamedHilbert.native_sentence_theorem
    functionSymbols relationSymbols bound A hp hresult.2
  exact hresult.1.symm ▸ hm

theorem instance_refutation_of_axioms_admissible (A : Carrier)
    (hPA : ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔)
    (φ : ArithmeticSemisentence 1) (n : ℕ)
    (h : 𝗣𝗔 ⊢ ∼(φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) :
    (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
      variableSymbols functionSymbols relationSymbols bound A).val.Evalb
        ![NamedArithmeticUnarySubstitution.value φ n] := by
  have hp := ArithmeticNamedProofTranslation.expanded_instance_refutation A hPA φ n h
  have hresult := standard_instance_result φ n
  have hm := SyntacticNamedHilbert.native_sentence_refutation
    functionSymbols relationSymbols bound A hp hresult.2
  exact hresult.1.symm ▸ hm

/-- Each standard computed theorem code has its own PA numeral proof.
This does not assert a PA proof of the universal Γ-bound sentence. -/
theorem instance_theorem_numeral_PA_of_axioms_admissible (A : Carrier)
    (hPA : ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔)
    (φ : ArithmeticSemisentence 1) (n : ℕ)
    (h : 𝗣𝗔 ⊢ (φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) :
    𝗣𝗔 ⊢ ((SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
      variableSymbols functionSymbols relationSymbols bound A).val/[
        (↑(NamedArithmeticUnarySubstitution.value φ n) : ArithmeticSemiterm Empty 0)] :
          ArithmeticSentence) := by
  have hp := ArithmeticNamedProofTranslation.expanded_instance_proof A hPA φ n h
  have hresult := standard_instance_result φ n
  rw [hresult.1]
  exact SyntacticNamedHilbert.native_sentence_numeral_PA
    functionSymbols relationSymbols bound A hp hresult.2

theorem instance_refutation_numeral_PA_of_axioms_admissible (A : Carrier)
    (hPA : ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔)
    (φ : ArithmeticSemisentence 1) (n : ℕ)
    (h : 𝗣𝗔 ⊢ ∼(φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) :
    𝗣𝗔 ⊢ ((SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
      variableSymbols functionSymbols relationSymbols bound A).val/[
        (↑(NamedArithmeticUnarySubstitution.value φ n) : ArithmeticSemiterm Empty 0)] :
          ArithmeticSentence) := by
  have hp := ArithmeticNamedProofTranslation.expanded_instance_refutation A hPA φ n h
  have hresult := standard_instance_result φ n
  rw [hresult.1]
  exact SyntacticNamedHilbert.native_refutation_numeral_PA
    functionSymbols relationSymbols bound A hp hresult.2

abbrev namedAlpha : Formula :=
  NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val

theorem namedAlpha_freeVariables : ∀ y, y ∈ namedAlpha.freeVariables → y = 0 :=
  NamedArithmeticUnarySubstitution.namedFormula_freeVariables ArithmeticDiagonalCodes.alpha.val

theorem standard_positive_of_axioms_admissible (A : Carrier)
    (hPA : ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔) (n : ℕ)
    (h : ArithmeticDiagonalCodes.alpha.val.Evalb (M := ℕ) ![n]) :
    (NamedArithmeticProofSearch.positive A namedAlpha).val.Evalb (M := ℕ) ![n] := by
  apply (NamedArithmeticProofSearch.positive_eval ℕ A namedAlpha n).mpr
  exact instance_theorem_of_axioms_admissible A hPA ArithmeticDiagonalCodes.alpha.val n
    (ArithmeticDiagonalCodes.output_numeral_PA 0 n h)

theorem standard_negative_of_axioms_admissible (A : Carrier)
    (hPA : ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔) (n : ℕ)
    (h : ArithmeticDiagonalCodes.beta.val.Evalb (M := ℕ) ![n]) :
    (NamedArithmeticProofSearch.negative A namedAlpha).val.Evalb (M := ℕ) ![n] := by
  apply (NamedArithmeticProofSearch.negative_literal_refutation
    ℕ A namedAlpha namedAlpha_freeVariables n).mpr
  exact instance_refutation_of_axioms_admissible A hPA ArithmeticDiagonalCodes.alpha.val n
    (ArithmeticDiagonalCodes.beta_numeral_refutes_alpha n h)

end CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds
