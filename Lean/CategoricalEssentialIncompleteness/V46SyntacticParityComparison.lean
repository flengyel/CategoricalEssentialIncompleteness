/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSearchLift
public import FailureOfComposition.TypedRecursionCategory

/-! # Even/odd comparison for the model coproduct and partial lift -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedRecursionCategory
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions

namespace CategoricalEssentialIncompleteness.V46.PartialSearchLift

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem mem_parity_encode_inl (x y : M) :
    y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (omegaCoprodIso 𝗣𝗔).hom (Sum.inl x) ↔
      y = 2 * x := by
  change y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map
    (arrowOfIndex 𝗣𝗔 (.coproduct .omega .omega) .omega omegaCoprodEncodeIndex) (Sum.inl x) ↔ _
  rw [SyntacticModel.mem_model_index]
  change (FailureOfComposition.ConcreteEvaluator.eventualGraph omegaCoprodEncodeIndex).val.Evalb
    ![pair x 0, y] ↔ _
  rw [eventualGraph_omegaCoprodEncodeIndex_eval]
  simp

theorem mem_parity_encode_inr (x y : M) :
    y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (omegaCoprodIso 𝗣𝗔).hom (Sum.inr x) ↔
      y = 2 * x + 1 := by
  change y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map
    (arrowOfIndex 𝗣𝗔 (.coproduct .omega .omega) .omega omegaCoprodEncodeIndex) (Sum.inr x) ↔ _
  rw [SyntacticModel.mem_model_index]
  change (FailureOfComposition.ConcreteEvaluator.eventualGraph omegaCoprodEncodeIndex).val.Evalb
    ![pair x 1, y] ↔ _
  rw [eventualGraph_omegaCoprodEncodeIndex_eval]
  simp

theorem mem_parity_decode_inl (x y : M) :
    Sum.inl y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (omegaCoprodIso 𝗣𝗔).inv x ↔
      x = 2 * y := by
  change Sum.inl y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map
    (arrowOfIndex 𝗣𝗔 .omega (.coproduct .omega .omega) omegaCoprodDecodeIndex) x ↔ _
  rw [SyntacticModel.mem_model_index]
  change (FailureOfComposition.ConcreteEvaluator.eventualGraph omegaCoprodDecodeIndex).val.Evalb
    ![x, pair y 0] ↔ _
  rw [eventualGraph_omegaCoprodDecodeIndex_eval, pair_eq_pair_iff]
  constructor
  · rintro ⟨hy, hr⟩
    have h := Arithmetic.div_add_mod x 2
    simpa only [← hy, ← hr, add_zero] using h.symm
  · rintro rfl
    simp

theorem mem_parity_decode_inr (x y : M) :
    Sum.inr y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (omegaCoprodIso 𝗣𝗔).inv x ↔
      x = 2 * y + 1 := by
  change Sum.inr y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map
    (arrowOfIndex 𝗣𝗔 .omega (.coproduct .omega .omega) omegaCoprodDecodeIndex) x ↔ _
  rw [SyntacticModel.mem_model_index]
  change (FailureOfComposition.ConcreteEvaluator.eventualGraph omegaCoprodDecodeIndex).val.Evalb
    ![x, pair y 1] ↔ _
  rw [eventualGraph_omegaCoprodDecodeIndex_eval, pair_eq_pair_iff]
  constructor
  · rintro ⟨hy, hr⟩
    have h := Arithmetic.div_add_mod x 2
    simpa only [← hy, ← hr] using h.symm
  · rintro rfl
    simp

/-- The same partial source morphism expressed in the manuscript's
numerical even/odd coproduct coordinates. -/
def parityLift (C D : Carrier) : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔 :=
  lift C D ≫ (omegaCoprodIso 𝗣𝗔).hom

theorem parityLift_decode (C D : Carrier) :
    parityLift C D ≫ (omegaCoprodIso 𝗣𝗔).inv = lift C D := by
  simp [parityLift, Category.assoc]

/-- The entire numerical partial graph agrees at every element of a PA
model, including nonstandard inputs and outputs. -/
theorem mem_parityLift (C D : Carrier)
    (hd : ∀ x : M, ¬(C.val.Evalb ![x] ∧ D.val.Evalb ![x])) (x y : M) :
    y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (parityLift C D) x ↔
      (C.val.Evalb ![x] ∧ y = 2 * x + 1) ∨ (D.val.Evalb ![x] ∧ y = 2 * x) := by
  rw [parityLift, (SyntacticModel.modelFunctor 𝗣𝗔 M).map_comp, mem_comp]
  change (∃ z : M ⊕ M,
    z ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (lift C D) x ∧
    y ∈ (SyntacticModel.modelFunctor 𝗣𝗔 M).map (omegaCoprodIso 𝗣𝗔).hom z) ↔ _
  constructor
  · rintro ⟨z, hz, hy⟩
    cases z with
    | inl a =>
      obtain ⟨hD, he⟩ := (mem_model_lift M C D hd x (Sum.inl a)).mp hz
      subst a
      exact Or.inr ⟨hD, (mem_parity_encode_inl M x y).mp hy⟩
    | inr a =>
      obtain ⟨hC, he⟩ := (mem_model_lift M C D hd x (Sum.inr a)).mp hz
      subst a
      exact Or.inl ⟨hC, (mem_parity_encode_inr M x y).mp hy⟩
  · rintro (⟨hC, hy⟩ | ⟨hD, hy⟩)
    · exact ⟨Sum.inr x, (mem_model_lift M C D hd x (Sum.inr x)).mpr ⟨hC, rfl⟩,
        (mem_parity_encode_inr M x y).mpr hy⟩
    · exact ⟨Sum.inl x, (mem_model_lift M C D hd x (Sum.inl x)).mpr ⟨hD, rfl⟩,
        (mem_parity_encode_inl M x y).mpr hy⟩

end CategoricalEssentialIncompleteness.V46.PartialSearchLift
