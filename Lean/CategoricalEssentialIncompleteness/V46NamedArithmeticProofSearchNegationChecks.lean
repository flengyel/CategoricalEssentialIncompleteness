/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchNegation

/-! # Printed PR-total negation and actual Γ negative evidence -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.NamedArithmeticSignature
open CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch.NegationChecks

example : Primrec (negationWord ℕ : ℕ → ℕ) := negationWord_primrec

example : 𝗣𝗔 ⊢ negationWordTotalitySentence := negationWord_total_PA

example (φ : Formula) :
    negationWord ℕ (NamedArithmeticSignature.formulaCode φ) =
      NamedArithmeticSignature.formulaCode (.neg φ) := negationWord_formulaCode φ

example (Γ : Carrier) (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (n : M) :
    (negative Γ φ).val.Evalb ![n] ↔
      (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound Γ).val.Evalb
          ![negationWord M (NamedArithmeticFixedSubstitution.value φ n)] :=
  negative_eval_word M Γ φ hφ n

end CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch.NegationChecks
