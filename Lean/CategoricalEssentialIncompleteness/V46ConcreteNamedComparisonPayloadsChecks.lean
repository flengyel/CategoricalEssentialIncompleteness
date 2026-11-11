/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPayloads

/-! # Actual projection arrows exist over an arbitrary name-parameter object -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (U V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

example (formula : Bool) : GraphMorphism T (payloadInputCarrier U V σ π d formula)
    (syntaxCarrier V σ π d formula) :=
  payloadProjectionMorphism T U V σ π d .original formula

example (formula : Bool) :
    constantFamily (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T))
        (syntaxCarrier V σ π d formula : PredicateCategory T) ⟶
      constantFamily (U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T))
        (CategoricalEssentialIncompleteness.V46.SyntacticLists.listObject T V) :=
  payloadProjectionFamily T U V σ π d .occurrences formula
