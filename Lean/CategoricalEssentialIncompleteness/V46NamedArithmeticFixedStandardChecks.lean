/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticFixedStandard


/-! # Standard output comparison for a generic finite named formula -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open NamedArithmeticSignature NamedArithmeticFixedSubstitution
example (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : ℕ) :
    ∃ out : Formula, φ.substitute 0 (numeral n) = some out ∧
      value φ n = NamedArithmeticSignature.formulaCode out ∧ out.freeVariables = [] :=
  standard_literal_result φ hφ n
