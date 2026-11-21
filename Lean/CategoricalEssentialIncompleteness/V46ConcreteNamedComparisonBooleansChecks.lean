/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonBooleans

/-! # Numeric Boolean records have the categorical truth points -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open CategoricalEssentialIncompleteness
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

example (X : PredicateCategory T) (b : Bool) :
    rawBooleanConstant T X b ≫ (SyntacticDecidableVariables.booleanIso T).hom =
      Two.constant X b := rawBooleanConstant_iso T X b
