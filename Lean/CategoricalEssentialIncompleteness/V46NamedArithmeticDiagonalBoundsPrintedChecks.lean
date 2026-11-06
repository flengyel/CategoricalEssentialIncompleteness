import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalBoundsPrinted

/-! # Exact Γ-extension hypothesis and whole-model bounds -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.NamedArithmeticSignature
open CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds
open CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparison

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds.PrintedChecks

example (A : Carrier)
    (hΓ : ∀ ψ : Formula,
      (ψ.freeVariables = [] ∧ ∃ φ, PASeed φ ∧ UniversalClosure φ ψ) →
      SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A ψ) :
    (ℕ↓[ℒₒᵣ] ⊧ positiveSentence A) ∧ (ℕ↓[ℒₒᵣ] ⊧ negativeSentence A) :=
  standard_sentences A hΓ

example (A : Carrier)
    (hΓ : ∀ ψ : Formula,
      (ψ.freeVariables = [] ∧ ∃ φ, PASeed φ ∧ UniversalClosure φ ψ) →
      SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A ψ)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M ≡ₑ[ℒₒᵣ] ℕ] :
    (∀ n : M, ArithmeticDiagonalCodes.alpha.val.Evalb ![n] →
      (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound A).val.Evalb
          ![NamedArithmeticUnarySubstitution.value ArithmeticDiagonalCodes.alpha.val n]) ∧
    (∀ n : M, ArithmeticDiagonalCodes.beta.val.Evalb ![n] →
      (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound A).val.Evalb
          ![NamedArithmeticProofSearch.negationWord M
            (NamedArithmeticUnarySubstitution.value ArithmeticDiagonalCodes.alpha.val n)]) :=
  semantic_bounds M A hΓ

example (A : Carrier)
    (hΓ : ∀ ψ : Formula,
      (ψ.freeVariables = [] ∧ ∃ φ, PASeed φ ∧ UniversalClosure φ ψ) →
      SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A ψ)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M ≡ₑ[ℒₒᵣ] ℕ] :
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem ArithmeticDiagonalCodes.a0 ≤
      (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
        (Idem.pull (NamedArithmeticProofSearch.sourceTheta
          (NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val)
          (NamedArithmeticUnarySubstitution.namedFormula_freeVariables
            ArithmeticDiagonalCodes.alpha.val))
          (predicateIdem 𝗣𝗔 (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound A))) ∧
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem ArithmeticDiagonalCodes.a1 ≤
      (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
        (Idem.pull (NamedArithmeticProofSearch.sourceTheta
          (NamedArithmeticUnarySubstitution.namedFormula ArithmeticDiagonalCodes.alpha.val)
          (NamedArithmeticUnarySubstitution.namedFormula_freeVariables
            ArithmeticDiagonalCodes.alpha.val))
          (predicateIdem 𝗣𝗔 (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound A))) :=
  ⟨model_positive M A hΓ,model_negative M A hΓ⟩

end CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds.PrintedChecks

open CategoricalEssentialIncompleteness.V46

example {I : Type} (U : Ultrafilter I) (A : Carrier)
    (hΓ : ∀ ψ : Formula,
      (ψ.freeVariables = [] ∧ ∃ φ, PASeed φ ∧ UniversalClosure φ ψ) →
      SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A ψ) :
    (∀ n : ArithmeticUltrapower.Model U, ArithmeticDiagonalCodes.alpha.val.Evalb ![n] →
      (NamedArithmeticProofSearch.positive A namedAlpha).val.Evalb ![n]) ∧
    (∀ n : ArithmeticUltrapower.Model U, ArithmeticDiagonalCodes.beta.val.Evalb ![n] →
      (NamedArithmeticProofSearch.negative A namedAlpha).val.Evalb ![n]) :=
  ⟨semantic_positive (ArithmeticUltrapower.Model U) A hΓ,
    semantic_negative (ArithmeticUltrapower.Model U) A hΓ⟩
