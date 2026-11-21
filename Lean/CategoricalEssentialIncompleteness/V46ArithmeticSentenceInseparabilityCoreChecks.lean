/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticSentenceInseparabilityCore


/-! # The categorical recursive-separator argument for Gamma words -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticSentenceInseparabilityCoreChecks
open ArithmeticSentenceInseparability NamedArithmeticSignature
example (A : SyntacticPredicates.Carrier) (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A) :
    ¬ ∃ R : Set ℕ, ComputablePred (· ∈ R) ∧
      {word : ℕ | (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound A).val.Evalb (M := ℕ) ![word]} ⊆ R ∧
      Disjoint R {word : ℕ | (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound A).val.Evalb (M := ℕ) ![word]} :=
  no_recursive_separator A hPA
example : theta = (NamedArithmeticUnarySubstitution.value (M := ℕ)
    ArithmeticDiagonalCodes.alpha.val : ℕ → ℕ) := rfl
example : theta = (NamedArithmeticFixedSubstitution.value (M := ℕ)
    NamedArithmeticDiagonalBounds.namedAlpha : ℕ → ℕ) := theta_eq_fixed_function
end CategoricalEssentialIncompleteness.V46.ArithmeticSentenceInseparabilityCoreChecks
