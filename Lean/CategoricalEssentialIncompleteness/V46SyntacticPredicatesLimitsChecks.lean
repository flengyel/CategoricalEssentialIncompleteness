/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticPredicatesLimits

/-! # Explicit predicate comparison statement checks -/

noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticPredicates.LimitsChecks

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example : HasFiniteLimits (PredicateCategory T) := inferInstance

example : HasFiniteLimits (TotalSplit T) := inferInstance

example : IsTerminal (C := PredicateCategory T) terminalCarrier := terminalIsTerminal T

example (C D : PredicateCategory T) :
    IsLimit (BinaryFan.mk (representedArrow T (productFst T C D))
      (representedArrow T (productSnd T C D))) := productIsLimit T C D

example {C D : PredicateCategory T} (f g : C ⟶ D) :
    IsLimit (Fork.ofι (equalizerInclusion T f g) (equalizer_condition T f g)) :=
  equalizerIsLimit T f g

end CategoricalEssentialIncompleteness.V46.SyntacticPredicates.LimitsChecks
