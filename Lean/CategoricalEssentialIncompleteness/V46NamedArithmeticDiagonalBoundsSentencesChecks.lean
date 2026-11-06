import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalBoundsSentences

/-! # Whole-carrier elementary-transfer statement checks -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.NamedArithmeticSignature
open CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds.SentenceChecks

example (A : Carrier)
    (hPA : ∀ ψ ∈ 𝗣𝗔, SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] ψ))
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M ≡ₑ[ℒₒᵣ] ℕ] :
    (∀ n : M, ArithmeticDiagonalCodes.alpha.val.Evalb ![n] →
      (NamedArithmeticProofSearch.positive A namedAlpha).val.Evalb ![n]) ∧
    (∀ n : M, ArithmeticDiagonalCodes.beta.val.Evalb ![n] →
      (NamedArithmeticProofSearch.negative A namedAlpha).val.Evalb ![n]) :=
  ⟨semantic_positive_of_axioms_admissible M A hPA,
    semantic_negative_of_axioms_admissible M A hPA⟩

end CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds.SentenceChecks
