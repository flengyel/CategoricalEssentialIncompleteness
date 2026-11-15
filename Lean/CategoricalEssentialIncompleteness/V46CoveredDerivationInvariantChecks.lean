/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46SignedDerivationInternalTruth

/-! # Independent checks of the coded invariant and actual rule geometry -/
@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
open SyntacticPredicates SyntacticLists

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {D C P Fm : PredicateCategory T}

example (support : D ⟶ C) (conclusion : D ⟶ Fm)
    (v : P ⨯ Fm ⟶ Two (PredicateCategory T)) (l : Obj T M P) (d : Obj T M D) :
    (CoveredDerivationInvariant.formula T M support conclusion v l).val.Eval ![d.val] id ↔
      ((∀ i < len ((F T M).map support d).val,
          MemVec (nth ((F T M).map support d).val i) l.val) →
        ∀ q : Obj T M (P ⨯ Fm),
          (F T M).map (prod.fst : P ⨯ Fm ⟶ P) q = l →
          (F T M).map (prod.snd : P ⨯ Fm ⟶ Fm) q = (F T M).map conclusion d →
          (F T M).map v q = (F T M).map (Two.constant (P ⨯ Fm) true) q) :=
  CoveredDerivationInvariant.formula_eval T M support conclusion v l d

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
example {W : PredicateCategory T} (f g : W ⟶ Two (PredicateCategory T)) (w : Obj T M W)
    (hf : (F T M).map f w = (F T M).map (Two.constant W true) w) :
    (F T M).map (Two.binary NullaryBooleanValuation.implies f g) w = (F T M).map g w :=
  ParameterizedBooleanModelTruth.implication_true_left T M f g w hf

#print axioms CoveredDerivationInvariant.TrueAt
#print axioms CoveredDerivationInvariant.trueAt_lift
#print axioms CoveredDerivationInvariant.formula
#print axioms CoveredDerivationInvariant.formula_eval
#print axioms CoveredDerivationInvariant.model_rule_induction
#print axioms ParameterizedBooleanModelTruth.implication_true_left
#print axioms ParameterizedBooleanModelTruth.logical_point
#print axioms ParameterizedBooleanModelTruth.modus_ponens_point
#print axioms ParameterizedBooleanModelTruth.generalization_point
#print axioms SignedDerivation.unary_child
#print axioms SignedDerivation.binary_first_child
#print axioms SignedDerivation.binary_second_child
#print axioms SignedDerivation.unary_child_conclusion
#print axioms SignedDerivation.binary_first_child_conclusion
#print axioms SignedDerivation.binary_second_child_conclusion
#print axioms SignedDerivation.unary_parent_conclusion
#print axioms SignedDerivation.binary_parent_conclusion
#print axioms SignedDerivation.nullary_label_constructor
#print axioms SignedDerivation.unary_support_value
#print axioms SignedDerivation.binary_support_value
#print axioms SignedDerivation.truth_from_leaves
