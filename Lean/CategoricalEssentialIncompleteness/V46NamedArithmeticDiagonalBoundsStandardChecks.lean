/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalBoundsStandard

/-! # Exact standard Γ proof witnesses at the computed diagonal sentence -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.NamedArithmeticSignature
open CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds.StandardChecks

example (A : Carrier)
    (hPA : ∀ ψ ∈ 𝗣𝗔, SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] ψ)) (n : ℕ)
    (h : ArithmeticDiagonalCodes.alpha.val.Evalb (M := ℕ) ![n]) :
    (NamedArithmeticProofSearch.positive A namedAlpha).val.Evalb (M := ℕ) ![n] :=
  standard_positive_of_axioms_admissible A hPA n h

example (A : Carrier)
    (hPA : ∀ ψ ∈ 𝗣𝗔, SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
      (ArithmeticNamedTranslation.translateFormula 0 ![] ψ)) (n : ℕ)
    (h : ArithmeticDiagonalCodes.beta.val.Evalb (M := ℕ) ![n]) :
    (NamedArithmeticProofSearch.negative A namedAlpha).val.Evalb (M := ℕ) ![n] :=
  standard_negative_of_axioms_admissible A hPA n h

end CategoricalEssentialIncompleteness.V46.NamedArithmeticDiagonalBounds.StandardChecks
