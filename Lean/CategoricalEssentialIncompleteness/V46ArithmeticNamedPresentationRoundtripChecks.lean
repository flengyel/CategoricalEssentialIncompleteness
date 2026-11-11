/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedPresentationRoundtrip


/-! # Statement checks in `V46ArithmeticNamedPresentationRoundtripChecks` -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
open NamedArithmeticSignature
example (A : SyntacticPredicates.Carrier) (n : ℕ) (φ : Formula) (hφ : ∀ x ∈ names φ, x < n)
    (seed : ℕ) (hn : n ≤ seed) :
    ArithmeticNamedProofConnectives.system A ⊢
      ArithmeticNamedOpenTranslation.formula seed ![] Fin.val (formula n φ) 🡘 φ :=
  formula_roundtrip A n φ hφ seed hn
example (A : SyntacticPredicates.Carrier) (φ : Formula) (hφ : φ.freeVariables = []) :
    ArithmeticNamedProofConnectives.system A ⊢
      ArithmeticNamedTranslation.translateFormula 0 ![] (sentence φ hφ) 🡘 φ :=
  sentence_zero_roundtrip A φ hφ
example (n : ℕ) (φ : Formula) (hφ : Bound n φ) (hc : φ.freeVariables = []) :
    (formula n φ).freeVariables = ∅ := formula_closed n φ hφ hc
end CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
