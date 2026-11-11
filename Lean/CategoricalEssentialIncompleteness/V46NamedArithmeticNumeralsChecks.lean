/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticNumerals


/-! # Statement checks in `V46NamedArithmeticNumeralsChecks` -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.NamedArithmeticNumerals
example : Primrec (numeralCode : ℕ → ℕ) := numeralCode_primrec
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (out n : M) :
    numeralGraph.val.Evalb ![out,n] ↔ out = numeralCode n := numeralGraph_eval out n
