/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FirstOrderLogicalInduction


/-! # Statement checks in `V46FirstOrderLogicalInductionChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.StandardInduction
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
variable {V : PredicateCategory T} {σ π : ℕ → PredicateCategory T} {d : ℕ}
variable (S : CategoricalSyntax V σ π d) (Q : Obj T M S.algebra.a.2 → Prop)

example
    (h₁ : ∀ z : Obj T M (S.algebra.a.2 ⨯ S.algebra.a.2), Q ((F T M).map S.hilbertOne z))
    (h₂ : ∀ z : Obj T M ((S.algebra.a.2 ⨯ S.algebra.a.2) ⨯ S.algebra.a.2),
      Q ((F T M).map S.hilbertTwo z))
    (h₃ : ∀ z : Obj T M (S.algebra.a.2 ⨯ S.algebra.a.2), Q ((F T M).map S.hilbertThree z))
    (h₄ : ∀ z : Obj T M S.instantiationParameters, Q ((F T M).map S.hilbertInstantiation z))
    (h₅ : ∀ z : Obj T M S.distributionParameters, Q ((F T M).map S.hilbertDistribution z))
    (h₆ : ∀ z : Obj T M S.algebra.a.1, Q ((F T M).map S.hilbertReflexivity z))
    (h₇ : ∀ z : Obj T M S.equalitySchemeParameters, Q ((F T M).map S.hilbertEquality z)) :
    ∀ l : Obj T M S.logicalParameters, Q ((F T M).map S.logicalAxioms l) :=
  logicalAxioms_predicate T M S Q h₁ h₂ h₃ h₄ h₅ h₆ h₇

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.StandardInduction
