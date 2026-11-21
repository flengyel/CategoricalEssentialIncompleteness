/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedPresentationBasic


/-! # Arithmetic named syntax presented by source NNF formulas -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
open NamedArithmeticSignature
example (φ : Formula) : (∀ x ∈ names φ, x < nameBound φ) := bound_nameBound φ
example {n x : ℕ} {φ : Formula} : Bound n (.all x φ) ↔ x < n ∧ Bound n φ := bound_all
example {n : ℕ} (x : Fin n) :
    Rew ℒₒᵣ (Fin n) 0 {y : Fin n // y ≠ x} 1 := bindRemove x
end CategoricalEssentialIncompleteness.V46.ArithmeticNamedPresentation
