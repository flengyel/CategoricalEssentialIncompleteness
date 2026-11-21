/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalBoundsUltrapower

/-! # Ultrapower model, without an assumed elementary-equivalence field -/

@[expose] public section
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
