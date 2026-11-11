/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalBoundsSentences
public import CategoricalEssentialIncompleteness.V46ArithmeticUltrapower

/-! # Elementary equivalence for the constructed arithmetic ultrapower -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic Filter
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds

/-- Łoś's sentence theorem gives the actual quotient's elementary
equivalence; it is not an additional hypothesis on the ultrapower. -/
instance ultrapower_elementary {I : Type} (U : Ultrafilter I) :
    ArithmeticUltrapower.Model U ≡ₑ[ℒₒᵣ] ℕ where
  models := ArithmeticUltrapower.sentence_iff U _

theorem ultrapower_sentences_of_axioms_admissible {I : Type} (U : Ultrafilter I)
    (A : Carrier) (hPA : ArithmeticNamedProofTranslation.AxiomsAdmissible A 𝗣𝗔) :
    ((ArithmeticUltrapower.Model U)↓[ℒₒᵣ] ⊧ positiveSentence A) ∧
      ((ArithmeticUltrapower.Model U)↓[ℒₒᵣ] ⊧ negativeSentence A) :=
  elementary_sentences_of_axioms_admissible (ArithmeticUltrapower.Model U) A hPA

end CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds
