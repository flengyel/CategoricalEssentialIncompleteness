import CategoricalEssentialIncompleteness.V46ArithmeticNamedProofNumerals

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedProofNumeralsChecks
open ArithmeticNamedProofNumerals

example (names : Fin 0 → ℕ) (n : ℕ) :
    ArithmeticNamedTranslation.translateTerm names (expandedNumeral n) =
      NamedArithmeticSignature.numeral n :=
  translate_expandedNumeral names n

example (n : ℕ) :
    𝗣𝗔 ⊢ (Semiformula.rel .eq ![expandedNumeral n,(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) :=
  expandedNumeral_eq_standard_PA n


example (φ : ArithmeticSemisentence 1) (n : ℕ) :
    𝗣𝗔 ⊢ ((φ/[expandedNumeral n] : ArithmeticSentence) 🡘
      (φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) :=
  expanded_instance_equivalence_PA φ n

example (φ : ArithmeticSemisentence 1) (n : ℕ)
    (h : 𝗣𝗔 ⊢ (φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) :
    𝗣𝗔 ⊢ (φ/[expandedNumeral n] : ArithmeticSentence) :=
  expanded_instance_PA φ n h

example (φ : ArithmeticSemisentence 1) (n : ℕ)
    (h : 𝗣𝗔 ⊢ ∼(φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) :
    𝗣𝗔 ⊢ ∼(φ/[expandedNumeral n] : ArithmeticSentence) :=
  expanded_instance_refutation_PA φ n h

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedProofNumeralsChecks
