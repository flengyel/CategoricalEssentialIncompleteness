/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonParameters

/-! # Both chosen input products have actual comparison arrows -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (V R C : PredicateCategory T)

example : @Quiver.Hom (PredicateCategory T) inferInstance ((V ⨯ R) ⨯ C)
    (productCarrier (productCarrier V R) C) := parameterInput T V R C

example : @Quiver.Hom (PredicateCategory T) inferInstance (C ⨯ (V ⨯ R))
    (productCarrier (productCarrier V R) C) := publicParameterInput T V R C
