/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedTranslation


/-! # Statement checks in `V46ArithmeticNamedTranslationChecks` -/

@[expose] public section
noncomputable section
universe w
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedTranslationChecks
open NamedArithmeticSignature ArithmeticNamedTranslation
variable {K : Type w} [ORingStructure K]

example {n : ℕ} (names : Fin n → ℕ) (t : ArithmeticSemiterm Empty n) (ρ : ℕ → K) :
    (translateTerm names t).evaluate functions ρ = t.val (s := Arithmetic.standardModel K) (fun i => ρ (names i)) Empty.elim :=
  evaluate_translateTerm names t ρ

example {n : ℕ} (names : Fin n → ℕ) (t : ArithmeticSemiterm Empty n)
    (x : ℕ) (hx : x ∈ (translateTerm names t).freeVariables) : ∃ i, names i = x :=
  translateTerm_freeVariables names t x hx

example (n : ℕ) (ρ : ℕ → K) :
    (numeral n).evaluate functions ρ = Nat.rec (0 : K) (fun _ previous => previous + 1) n :=
  evaluate_numeral n ρ

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedTranslationChecks
