/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FirstOrderStandardInduction
public import CategoricalEssentialIncompleteness.V46LogicalSchemes

/-! # Predicates on the seven logical scheme families -/

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

/-- Each point of the logical-axiom coproduct belongs to one of its seven specified
parameter families. -/
theorem logicalAxioms_predicate
    (h₁ : ∀ z : Obj T M (S.algebra.a.2 ⨯ S.algebra.a.2), Q ((F T M).map S.hilbertOne z))
    (h₂ : ∀ z : Obj T M ((S.algebra.a.2 ⨯ S.algebra.a.2) ⨯ S.algebra.a.2),
      Q ((F T M).map S.hilbertTwo z))
    (h₃ : ∀ z : Obj T M (S.algebra.a.2 ⨯ S.algebra.a.2), Q ((F T M).map S.hilbertThree z))
    (h₄ : ∀ z : Obj T M S.instantiationParameters, Q ((F T M).map S.hilbertInstantiation z))
    (h₅ : ∀ z : Obj T M S.distributionParameters, Q ((F T M).map S.hilbertDistribution z))
    (h₆ : ∀ z : Obj T M S.algebra.a.1, Q ((F T M).map S.hilbertReflexivity z))
    (h₇ : ∀ z : Obj T M S.equalitySchemeParameters, Q ((F T M).map S.hilbertEquality z)) :
    ∀ l : Obj T M S.logicalParameters, Q ((F T M).map S.logicalAxioms l) := by
  intro l
  unfold CategoricalSyntax.logicalAxioms
  apply model_copair_predicate T M _ _ Q
  · intro z
    apply model_copair_predicate T M _ _ Q
    · intro z
      apply model_copair_predicate T M _ _ Q
      · intro z
        apply model_copair_predicate T M _ _ Q
        · intro z
          apply model_copair_predicate T M _ _ Q
          · intro z
            apply model_copair_predicate T M _ _ Q
            · exact h₁
            · exact h₂
          · exact h₃
        · exact h₄
      · exact h₅
    · exact h₆
  · exact h₇

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.StandardInduction
