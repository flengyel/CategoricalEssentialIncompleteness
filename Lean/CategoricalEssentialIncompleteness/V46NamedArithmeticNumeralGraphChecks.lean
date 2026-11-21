/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticNumeralGraph


/-! # The numeral words define a PA-total morphism into the closed term predicate -/

@[expose] public section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.NamedArithmeticNumerals
example : SyntacticPredicates.GraphMorphism 𝗣𝗔 NamedArithmeticSignature.variableSymbols closedTermCarrier := numeralMorphism
example (n : ℕ) : numeralCode n = NamedArithmeticSignature.termCode (NamedArithmeticSignature.numeral n) :=
  numeralCode_standard n
