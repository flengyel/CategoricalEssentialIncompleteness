/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainFreeForTheory


/-! # Statement checks in `V46ConcreteNamedComparisonPlainFreeForTheoryChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.PlainFreeForTheoryChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

example : T ⊢ plainFreeForDomainSentence T V σ π d :=
  plainFreeForDomain_theory T V σ π d

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (input : M) :
    (plainAdmissibleCarrier T V σ π d).val.Evalb ![input] ↔
      (plainFreeForPredicate T V σ π d).val.Evalb ![input] :=
  plainAdmissibleCarrier_freeFor T V σ π d M input
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.PlainFreeForTheoryChecks
