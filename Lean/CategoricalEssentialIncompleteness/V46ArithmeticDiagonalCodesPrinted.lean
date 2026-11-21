/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalCodesTuring
public import CategoricalEssentialIncompleteness.V46PrintedObjectCodingModels

/-! # The chosen diagonal in exponential-product and parity coordinates -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedTuringMorphism
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalCodes

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- The comparison functor turns the chosen diagonal into the exponential diagonal of the
formal product. -/
theorem printed_diagonal (x z : M) :
    SyntacticModel.programRelation 𝗣𝗔 M
      ((PrintedObjectCoding.comparison 𝗣𝗔).map
        (PCategoryStruct.diag (omegaObject 𝗣𝗔))).hom.val x z ↔
      z = ExponentialPairing.code x x := by
  obtain ⟨a,b,rfl⟩ := ExponentialPairing.code_surjective z
  have h := PrintedObjectCoding.comparison_model 𝗣𝗔 M
    (PCategoryStruct.diag (omegaObject 𝗣𝗔)) x (a,b)
  change SyntacticModel.programRelation 𝗣𝗔 M _ x (ExponentialPairing.code a b) ↔
    SyntacticModel.programRelation 𝗣𝗔 M _ x (pair a b) at h
  rw [h]
  have hd := mem_source_diagonal M x (a,b)
  rw [mem_model_relation] at hd
  change SyntacticModel.programRelation 𝗣𝗔 M _ x (pair a b) ↔ (a,b) = (x,x) at hd
  rw [hd]
  constructor
  · intro he
    cases he
    rfl
  · intro he
    obtain ⟨ha,hb⟩ := ExponentialPairing.code_injective he
    exact Prod.ext ha hb

/-- The selected source Turing morphism is conjugated by the proved product isomorphism
and applies exactly the internal program index. -/
theorem printed_tau (a b y : M) :
    SyntacticModel.programRelation 𝗣𝗔 M
      ((PrintedObjectCoding.comparison 𝗣𝗔).map sourceTau).hom.val
        (ExponentialPairing.code a b) y ↔
      UniformTrace.graph.val.Evalb ![a,b,y] := by
  have h := PrintedObjectCoding.comparison_model 𝗣𝗔 M sourceTau (a,b) y
  change SyntacticModel.programRelation 𝗣𝗔 M _ (ExponentialPairing.code a b) y ↔
    SyntacticModel.programRelation 𝗣𝗔 M sourceTau.val (pair a b) y at h
  exact h.trans (sourceTau_relation M a b y)

theorem printed_tau_program (input y : M) :
    SyntacticModel.programRelation 𝗣𝗔 M
      ((PrintedObjectCoding.comparison 𝗣𝗔).map sourceTau).hom.val input y ↔
      UniformTrace.graph.val.Evalb ![(UniformTrace.universalIndex : M),input,y] := by
  obtain ⟨a,b,rfl⟩ := ExponentialPairing.code_surjective input
  exact (printed_tau M a b y).trans (UniformTrace.universal_eval a b y).symm

/-- The source even/odd decoding isomorphism has the identity numerical graph after the
recursive sum-coordinate comparison. -/
theorem printed_parity_program (input output : M) :
    SyntacticModel.programRelation 𝗣𝗔 M
      ((PrintedObjectCoding.comparison 𝗣𝗔).map
        (TypedRecursionCategory.omegaCoprodIso 𝗣𝗔).inv).hom.val input output ↔
      output = input := by
  obtain ⟨s,rfl⟩ := (PrintedObjectCoding.value_bijective 𝗣𝗔 M
    (.coproduct .omega .omega)).2 output
  have h := PrintedObjectCoding.comparison_model 𝗣𝗔 M
    (TypedRecursionCategory.omegaCoprodIso 𝗣𝗔).inv input s
  cases s with
  | inl m =>
      have hb := PartialSearchLift.mem_parity_decode_inl M input m
      rw [mem_model_relation] at hb
      exact (h.trans hb).trans eq_comm
  | inr m =>
      have hb := PartialSearchLift.mem_parity_decode_inr M input m
      rw [mem_model_relation] at hb
      exact (h.trans hb).trans eq_comm

theorem printed_sourceDiagonal (x y : M) :
    SyntacticModel.programRelation 𝗣𝗔 M
      ((PrintedObjectCoding.comparison 𝗣𝗔).map sourceDiagonal).hom.val x y ↔
      UniformTrace.graph.val.Evalb ![(diagonalIndex : M),x,y] := by
  have h := PrintedObjectCoding.comparison_model 𝗣𝗔 M sourceDiagonal x y
  have hs := mem_sourceDiagonal M x y
  rw [mem_model_relation] at hs
  exact h.trans hs

/-- In sum coordinates the even-output part is exactly alpha's output graph, with no
standardness restriction. -/
theorem printed_parity_inl (x m : M) :
    SyntacticModel.programRelation 𝗣𝗔 M
      ((PrintedObjectCoding.comparison 𝗣𝗔).map sourceParityDiagonal).hom.val x (2 * m) ↔
      UniformTrace.graph.val.Evalb ![(diagonalIndex : M),x,2 * m] := by
  have h := PrintedObjectCoding.comparison_model 𝗣𝗔 M sourceParityDiagonal x (Sum.inl m)
  have hs := mem_sourceParityDiagonal_inl M x m
  rw [mem_model_relation] at hs
  exact h.trans hs

theorem printed_parity_inr (x m : M) :
    SyntacticModel.programRelation 𝗣𝗔 M
      ((PrintedObjectCoding.comparison 𝗣𝗔).map sourceParityDiagonal).hom.val x (2 * m + 1) ↔
      UniformTrace.graph.val.Evalb ![(diagonalIndex : M),x,2 * m + 1] := by
  have h := PrintedObjectCoding.comparison_model 𝗣𝗔 M sourceParityDiagonal x (Sum.inr m)
  have hs := mem_sourceParityDiagonal_inr M x m
  rw [mem_model_relation] at hs
  exact h.trans hs

end Models

/-- In the manuscript's numerical object coordinates, the Turing morphism is exactly the
morphism of the universal program index. -/
theorem printed_tau_is_universal :
    ((PrintedObjectCoding.comparison 𝗣𝗔).map sourceTau).hom =
      arrowOfIndex 𝗣𝗔 .omega .omega UniformTrace.universalIndex := by
  apply CodedHom.ext
  apply SyntacticPredicates.programClass_ext 𝗣𝗔
  intro M _ _ input y
  exact (printed_tau_program M input y).trans (universal_arrow_relation M input y).symm

theorem printed_parity_is_identity :
    ((PrintedObjectCoding.comparison 𝗣𝗔).map
      (TypedRecursionCategory.omegaCoprodIso 𝗣𝗔).inv).hom = 𝟙 (omegaObject 𝗣𝗔) := by
  apply CodedHom.ext
  apply SyntacticPredicates.programClass_ext 𝗣𝗔
  intro M _ _ input output
  rw [printed_parity_program,id_val,SyntacticModel.object_relation]
  change output = input ↔
    (CodedObjectMembership.memberFormula .omega).val.Evalb ![input] ∧ output = input
  simp only [CodedObjectMembership.memberFormula_omega_eval,true_and]

end CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalCodes
