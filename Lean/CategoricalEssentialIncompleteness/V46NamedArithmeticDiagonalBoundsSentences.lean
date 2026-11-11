/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalBoundsStandard
public import Foundation.FirstOrder.Tarski.Elementary

/-! # Fixed universal diagonal-bound sentences and elementary transfer

These are standard truth statements, not assertions that PA proves the
uniform Γ bounds. Elementary equivalence transfers their universal
closures and hence covers every internal element of the target model.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds

def positiveSentence (A : Carrier) : ArithmeticSentence :=
  let α := ArithmeticDiagonalCodes.alpha
  let C := NamedArithmeticProofSearch.positive A namedAlpha
  “∀ n, !α.val n → !C.val n”

def negativeSentence (A : Carrier) : ArithmeticSentence :=
  let β := ArithmeticDiagonalCodes.beta
  let C := NamedArithmeticProofSearch.negative A namedAlpha
  “∀ n, !β.val n → !C.val n”

@[simp] theorem positiveSentence_models (A : Carrier) (M : Type) [ORingStructure M] :
    M↓[ℒₒᵣ] ⊧ positiveSentence A ↔
      ∀ n : M, ArithmeticDiagonalCodes.alpha.val.Evalb ![n] →
        (NamedArithmeticProofSearch.positive A namedAlpha).val.Evalb ![n] := by
  simp [models_iff,positiveSentence]

@[simp] theorem negativeSentence_models (A : Carrier) (M : Type) [ORingStructure M] :
    M↓[ℒₒᵣ] ⊧ negativeSentence A ↔
      ∀ n : M, ArithmeticDiagonalCodes.beta.val.Evalb ![n] →
        (NamedArithmeticProofSearch.negative A namedAlpha).val.Evalb ![n] := by
  simp [models_iff,negativeSentence]

theorem standard_sentences_of_axioms_admissible (A : Carrier)
    (hPA : ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔) :
    (ℕ↓[ℒₒᵣ] ⊧ positiveSentence A) ∧ (ℕ↓[ℒₒᵣ] ⊧ negativeSentence A) := by
  exact ⟨(positiveSentence_models A ℕ).mpr
      (fun n h => standard_positive_of_axioms_admissible A hPA n h),
    (negativeSentence_models A ℕ).mpr
      (fun n h => standard_negative_of_axioms_admissible A hPA n h)⟩

section Elementary

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable [M ≡ₑ[ℒₒᵣ] ℕ]

/-- The same fixed two arithmetic sentences hold in every elementary
equivalent code model, without any PA proof of Γ's consistency. -/
theorem elementary_sentences_of_axioms_admissible (A : Carrier)
    (hPA : ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔) :
    (M↓[ℒₒᵣ] ⊧ positiveSentence A) ∧ (M↓[ℒₒᵣ] ⊧ negativeSentence A) := by
  have hN := standard_sentences_of_axioms_admissible A hPA
  exact ⟨Tarski.Structure.ElementaryEquiv.models.mpr hN.1,
    Tarski.Structure.ElementaryEquiv.models.mpr hN.2⟩

theorem semantic_positive_of_axioms_admissible (A : Carrier)
    (hPA : ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔) (n : M)
    (h : ArithmeticDiagonalCodes.alpha.val.Evalb ![n]) :
    (NamedArithmeticProofSearch.positive A namedAlpha).val.Evalb ![n] :=
  (positiveSentence_models A M).mp
    (elementary_sentences_of_axioms_admissible M A hPA).1 n h

theorem semantic_negative_of_axioms_admissible (A : Carrier)
    (hPA : ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔) (n : M)
    (h : ArithmeticDiagonalCodes.beta.val.Evalb ![n]) :
    (NamedArithmeticProofSearch.negative A namedAlpha).val.Evalb ![n] :=
  (negativeSentence_models A M).mp
    (elementary_sentences_of_axioms_admissible M A hPA).2 n h

end Elementary
end CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds
