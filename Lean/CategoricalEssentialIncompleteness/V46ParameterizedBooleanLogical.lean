/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ParameterizedBooleanEquations
public import CategoricalEssentialIncompleteness.V46NullaryBooleanTruthTables

/-! # Logical Boolean computations with a shared internal parameter -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ParameterizedBooleanValuation
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0) (P : D)
variable (d : constantFamily P X ⟶ constantFamily P (Two D))
variable {W : D} (p : W ⟶ P)

/-- The first propositional scheme at any shared support parameter. -/
theorem hilbert_one_value (a : W ⟶ S.algebra.a.2 ⨯ S.algebra.a.2) :
    evaluate S P d p (a ≫ S.hilbertOne) = Two.constant W true := by
  simp only [CategoricalSyntax.hilbertOne, ← Category.assoc, prod.comp_lift,
    evaluate_implication_input, prod.lift_fst, prod.lift_snd]
  exact NullaryBooleanValuation.implication_one (D := D) _ _

/-- The second propositional scheme at any shared support parameter. -/
theorem hilbert_two_value (a : W ⟶ (S.algebra.a.2 ⨯ S.algebra.a.2) ⨯ S.algebra.a.2) :
    evaluate S P d p (a ≫ S.hilbertTwo) = Two.constant W true := by
  simp only [CategoricalSyntax.hilbertTwo, ← Category.assoc, prod.comp_lift,
    evaluate_implication_input, prod.lift_fst, prod.lift_snd]
  exact NullaryBooleanValuation.implication_two (D := D) _ _ _

/-- The classical propositional scheme at any shared support parameter. -/
theorem hilbert_three_value (a : W ⟶ S.algebra.a.2 ⨯ S.algebra.a.2) :
    evaluate S P d p (a ≫ S.hilbertThree) = Two.constant W true := by
  simp only [CategoricalSyntax.hilbertThree, ← Category.assoc, prod.comp_lift,
    evaluate_implication_input, evaluate_negation, prod.lift_fst, prod.lift_snd]
  exact NullaryBooleanValuation.implication_three (D := D) _ _

/-- Quantifier distribution has the value of an implication to itself. -/
theorem hilbert_distribution_value (a : W ⟶ S.distributionParameters) :
    evaluate S P d p (a ≫ S.hilbertDistribution) = Two.constant W true := by
  simp only [CategoricalSyntax.hilbertDistribution, ← Category.assoc, prod.comp_lift,
    evaluate_implication_input, evaluate_quantifier_input, prod.lift_fst, prod.lift_snd]
  exact NullaryBooleanValuation.implication_self (D := D) _

/-- Every equality, and hence the reflexivity scheme, has value true. -/
theorem hilbert_reflexivity_value (a : W ⟶ S.algebra.a.1) :
    evaluate S P d p (a ≫ S.hilbertReflexivity) = Two.constant W true := by
  simp only [CategoricalSyntax.hilbertReflexivity, ← Category.assoc, prod.comp_lift,
    evaluate_equality, Category.comp_id]

/-- Modus ponens preserves truth at the same internal parameter. -/
theorem modus_ponens_truth (f g : W ⟶ S.algebra.a.2)
    (hf : evaluate S P d p f = Two.constant W true)
    (hi : evaluate S P d p (prod.lift f g ≫ S.implicationConstructor) =
      Two.constant W true) : evaluate S P d p g = Two.constant W true := by
  rw [evaluate_implication, hf, NullaryBooleanValuation.implication_true_left] at hi
  exact hi

/-- Generalization preserves truth without changing the support parameter. -/
theorem generalization_truth (v : W ⟶ V) (f : W ⟶ S.algebra.a.2)
    (hf : evaluate S P d p f = Two.constant W true) :
    evaluate S P d p (prod.lift v f ≫ S.quantifierConstructor) = Two.constant W true :=
  (evaluate_quantifier S P d p v f).trans hf

end CategoricalEssentialIncompleteness.V46.ParameterizedBooleanValuation
