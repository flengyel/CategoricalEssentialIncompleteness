/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.SyntacticModel

/-! # Preservation on the recursively interpreted model carriers -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open FailureOfComposition.CodedObjectMembership FailureOfComposition.ConcreteEvaluator

namespace CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel

open PartialFunctions

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

theorem mem_model {Q R : CodedProgramCategory T} (f : Q ⟶ R)
    (x : interpretedType M (objectCode Q)) (y : interpretedType M (objectCode R)) :
    y ∈ (modelFunctor T M).map f x ↔
      codingEquiv T M (objectCode R) y ∈
        (functor T M).map f (codingEquiv T M (objectCode Q) x) :=
  mem_conjugate _ _ _ x y

theorem mem_model_index (Q R : STObjectCode) (q : ℕ)
    (x : interpretedType M Q) (y : interpretedType M R) :
    y ∈ (modelFunctor T M).map (arrowOfIndex T Q R q) x ↔
      (eventualGraph q).val.Evalb
        ![(codingEquiv T M Q x).val, (codingEquiv T M R y).val] := by
  rw [mem_model, mem_map_index]
  rfl

theorem model_map_restriction {Q R : CodedProgramCategory T} (f : Q ⟶ R) :
    (modelFunctor T M).map (rst f) = rst ((modelFunctor T M).map f) := by
  apply PFun.ext
  intro x y
  rw [mem_model, map_restriction, mem_rst, mem_rst]
  constructor
  · rintro ⟨⟨z, hz⟩, he⟩
    refine ⟨⟨(codingEquiv T M (objectCode R)).symm z, ?_⟩,
      (codingEquiv T M (objectCode Q)).injective he⟩
    rw [mem_model, Equiv.apply_symm_apply]
    exact hz
  · rintro ⟨⟨z, hz⟩, he⟩
    exact ⟨⟨codingEquiv T M (objectCode R) z, (mem_model T M f x z).mp hz⟩,
      congrArg (codingEquiv T M (objectCode Q)) he⟩

theorem model_map_range {Q R : CodedProgramCategory T} (f : Q ⟶ R) :
    (modelFunctor T M).map (Ranges.range f).hom =
      (Ranges.range ((modelFunctor T M).map f)).hom := by
  apply PFun.ext
  intro y z
  rw [mem_model, map_range, mem_range, mem_range]
  constructor
  · rintro ⟨⟨x, hx⟩, he⟩
    refine ⟨⟨(codingEquiv T M (objectCode Q)).symm x, ?_⟩,
      (codingEquiv T M (objectCode R)).injective he⟩
    rw [mem_model, Equiv.apply_symm_apply]
    exact hx
  · rintro ⟨⟨x, hx⟩, he⟩
    exact ⟨⟨codingEquiv T M (objectCode Q) x, (mem_model T M f x y).mp hx⟩,
      congrArg (codingEquiv T M (objectCode R)) he⟩

theorem model_map_zero (Q R : CodedProgramCategory T) :
    (modelFunctor T M).map (0 : Q ⟶ R) = 0 := by
  apply PFun.ext
  intro x y
  rw [mem_model, map_zero, mem_zero, mem_zero]

theorem model_map_i0 (Q R : CodedProgramCategory T) :
    (modelFunctor T M).map (i0 Q R) =
      i0 ((modelFunctor T M).obj Q) ((modelFunctor T M).obj R) := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  apply PFun.ext
  intro x y
  change y ∈ (modelFunctor T M).map (arrowOfIndex T (objectCode Q)
    (.coproduct (objectCode Q) (objectCode R)) (TypedCoproducts.leftInjectionIndex _)) x ↔ _
  rw [mem_model_index, TypedCoproducts.eventualGraph_leftInjectionIndex_eval,
    i0_apply, Part.mem_some_iff]
  constructor
  · intro h
    apply (codingEquiv T M (.coproduct (objectCode Q) (objectCode R))).injective
    exact Subtype.ext h.2
  · intro h
    subst y
    exact ⟨(codingEquiv T M (objectCode Q) x).property, rfl⟩

theorem model_map_i1 (Q R : CodedProgramCategory T) :
    (modelFunctor T M).map (i1 Q R) =
      i1 ((modelFunctor T M).obj Q) ((modelFunctor T M).obj R) := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  apply PFun.ext
  intro x y
  change y ∈ (modelFunctor T M).map (arrowOfIndex T (objectCode R)
    (.coproduct (objectCode Q) (objectCode R)) (TypedCoproducts.rightInjectionIndex _)) x ↔ _
  rw [mem_model_index, TypedCoproducts.eventualGraph_rightInjectionIndex_eval,
    i1_apply, Part.mem_some_iff]
  constructor
  · intro h
    apply (codingEquiv T M (.coproduct (objectCode Q) (objectCode R))).injective
    exact Subtype.ext h.2
  · intro h
    subst y
    exact ⟨(codingEquiv T M (objectCode R) x).property, rfl⟩

theorem model_comparison_eq_id (Q R : CodedProgramCategory T) :
    coproductComparison (modelFunctor T M) Q R =
      𝟙 (coprod ((modelFunctor T M).obj Q) ((modelFunctor T M).obj R)) := by
  rw [coproductComparison, model_map_i0, model_map_i1, copair_i0_i1]

/-- Proposition 4.1: the functor on the recursively interpreted carriers
preserves restrictions, ranges, zeros and binary restriction coproducts. -/
def modelRangeFunctor : RangeFunctor (CodedProgramCategory T) Pfn where
  toFunctor := modelFunctor T M
  map_restrict := model_map_restriction T M
  map_range := model_map_range T M
  map_zero := model_map_zero T M
  comparison_isIso Q R := by rw [model_comparison_eq_id]; infer_instance

theorem model_map_product {Q R S V : CodedProgramCategory T} (f : Q ⟶ R) (g : S ⟶ V) :
    (modelFunctor T M).map (PCategoryStruct.nearProd_map f g) =
      PFun.prodMap ((modelFunctor T M).map f) ((modelFunctor T M).map g) := by
  obtain ⟨q, rfl⟩ := exists_arrowOfIndex T (objectCode Q) (objectCode R) f
  obtain ⟨r, rfl⟩ := exists_arrowOfIndex T (objectCode S) (objectCode V) g
  apply PFun.ext
  intro x y
  rw [mem_model, PFun.mem_prodMap, mem_model, mem_model]
  exact map_product_graph T M _ _ _ _ q r
    (codingEquiv T M _ x.1) (codingEquiv T M _ x.2)
    (codingEquiv T M _ y.1) (codingEquiv T M _ y.2)

theorem model_map_first_projection (Q R : STObjectCode) :
    (modelFunctor T M).map (PCategoryStruct.p0 (object T Q) (object T R)) =
      PFun.lift (Prod.fst : interpretedType M Q × interpretedType M R → interpretedType M Q) := by
  apply PFun.ext
  intro x y
  rw [mem_model]
  change codingEquiv T M Q y ∈
    (functor T M).map (PCategoryStruct.p0 (object T Q) (object T R))
    (productCoding T M Q R (codingEquiv T M Q x.1, codingEquiv T M R x.2)) ↔ _
  rw [map_first_projection]
  simp only [PFun.lift, Part.mem_some_iff]
  change codingEquiv T M Q y = codingEquiv T M Q x.1 ↔ y = x.1
  exact (codingEquiv T M Q).injective.eq_iff

theorem model_map_second_projection (Q R : STObjectCode) :
    (modelFunctor T M).map (PCategoryStruct.p1 (object T Q) (object T R)) =
      PFun.lift (Prod.snd : interpretedType M Q × interpretedType M R → interpretedType M R) := by
  apply PFun.ext
  intro x y
  rw [mem_model]
  change codingEquiv T M R y ∈
    (functor T M).map (PCategoryStruct.p1 (object T Q) (object T R))
    (productCoding T M Q R (codingEquiv T M Q x.1, codingEquiv T M R x.2)) ↔ _
  rw [map_second_projection]
  simp only [PFun.lift, Part.mem_some_iff]
  change codingEquiv T M R y = codingEquiv T M R x.2 ↔ y = x.2
  exact (codingEquiv T M R).injective.eq_iff

theorem model_map_sup {Q : CodedProgramCategory T} (a b : Idem Q) :
    (modelRangeFunctor T M).mapIdem (a ⊔ b) =
      (modelRangeFunctor T M).mapIdem a ⊔ (modelRangeFunctor T M).mapIdem b :=
  (modelRangeFunctor T M).map_sup a b

end CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel
