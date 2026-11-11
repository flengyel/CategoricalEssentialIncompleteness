/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticNumeralCarriers


/-! # Statement checks in `V46NamedArithmeticNumeralCarriersChecks` -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.NamedArithmeticNumerals
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (n : M) :
    termCarrier.val.Evalb ![numeralCode n] ∧ occurrences M (numeralCode n) = 0 :=
  numeralCode_carrier_closed n
