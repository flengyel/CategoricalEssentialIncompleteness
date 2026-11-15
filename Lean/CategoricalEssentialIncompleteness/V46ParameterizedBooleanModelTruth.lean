/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ParameterizedBooleanLogicalSoundness
public import CategoricalEssentialIncompleteness.V46CoveredDerivationInvariant
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonModels

/-! # Logical truth at arbitrary arithmetic-model inputs -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ParameterizedBooleanModelTruth
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- A true antecedent reduces implication to its consequent at that point.
The pointwise premise need not hold at other elements of the source. -/
theorem implication_true_left {W : PredicateCategory T}
    (f g : W ⟶ Two (PredicateCategory T)) (w : Obj T M W)
    (hf : (F T M).map f w = (F T M).map (Two.constant W true) w) :
    (F T M).map (Two.binary NullaryBooleanValuation.implies f g) w =
      (F T M).map g w := by
  have he : (F T M).map (prod.lift f g) w =
      (F T M).map (prod.lift (Two.constant W true) g) w := by
    apply modelProduct_ext T M
    · simpa only [ConcreteNamedComparison.model_lift_fst] using hf
    · simp only [ConcreteNamedComparison.model_lift_snd]
  change (F T M).map (prod.lift f g ≫ Two.binaryArrow _) w = _
  rw [Functor.map_comp_apply, he, ← Functor.map_comp_apply]
  change (F T M).map (Two.binary NullaryBooleanValuation.implies
    (Two.constant W true) g) w = _
  rw [NullaryBooleanValuation.implication_true_left]

variable {V X : PredicateCategory T}
variable (S : CategoricalSyntax V (fun _ => ⊥_ (PredicateCategory T)) (fun _ => X) 0)
variable (P : PredicateCategory T)
variable (d : constantFamily P X ⟶ constantFamily P (Two (PredicateCategory T)))
variable {W : PredicateCategory T} (p : W ⟶ P)
open ParameterizedBooleanValuation

/-- All seven scheme branches hold at every internal input. -/
theorem logical_point (a : W ⟶ S.logicalParameters) (w : Obj T M W) :
    (F T M).map (evaluate S P d p (a ≫ S.logicalAxioms)) w =
      (F T M).map (Two.constant W true) w := by
  rw [logical_axioms_value]

/-- Modus ponens at an internal input, with the same support in both premises. -/
theorem modus_ponens_point (f g : W ⟶ S.algebra.a.2) (w : Obj T M W)
    (hf : (F T M).map (evaluate S P d p f) w =
      (F T M).map (Two.constant W true) w)
    (hi : (F T M).map
      (evaluate S P d p (prod.lift f g ≫ S.implicationConstructor)) w =
        (F T M).map (Two.constant W true) w) :
    (F T M).map (evaluate S P d p g) w =
      (F T M).map (Two.constant W true) w := by
  rw [evaluate_implication] at hi
  exact (implication_true_left T M (evaluate S P d p f) (evaluate S P d p g) w hf).symm.trans hi

/-- Generalization at the same internal support. -/
theorem generalization_point (x : W ⟶ V) (f : W ⟶ S.algebra.a.2) (w : Obj T M W)
    (hf : (F T M).map (evaluate S P d p f) w =
      (F T M).map (Two.constant W true) w) :
    (F T M).map (evaluate S P d p (prod.lift x f ≫ S.quantifierConstructor)) w =
      (F T M).map (Two.constant W true) w := by
  rw [evaluate_quantifier]
  exact hf

end CategoricalEssentialIncompleteness.V46.ParameterizedBooleanModelTruth
