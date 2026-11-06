import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalBoundsUltrapower

/-! # Actual ultrapower model, without an assumed elementary-equivalence field -/
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic Filter
open CategoricalEssentialIncompleteness.V46

example {I : Type} (U : Ultrafilter I) :
    ArithmeticUltrapower.Model U ≡ₑ[ℒₒᵣ] ℕ := inferInstance

example {I : Type} (U : Ultrafilter I)
    (A : SyntacticPredicates.Carrier)
    (hPA : ∀ ψ ∈ 𝗣𝗔, SyntacticNamedHilbert.Derives
      NamedArithmeticSignature.functionSymbols NamedArithmeticSignature.relationSymbols
      NamedArithmeticSignature.bound A (ArithmeticNamedTranslation.translateFormula 0 ![] ψ)) :
    ((ArithmeticUltrapower.Model U)↓[ℒₒᵣ] ⊧ NamedArithmeticDiagonalBounds.positiveSentence A) ∧
      ((ArithmeticUltrapower.Model U)↓[ℒₒᵣ] ⊧ NamedArithmeticDiagonalBounds.negativeSentence A) :=
  NamedArithmeticDiagonalBounds.ultrapower_sentences_of_axioms_admissible U A hPA
