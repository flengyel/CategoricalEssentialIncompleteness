/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticPredicates
public import CategoricalEssentialIncompleteness.SyntacticPreservation

/-! # Source restriction predicates and graph inverse images

The inverse-image comparison is equality in the source quotient, proved
uniformly in all models of the ambient theory. The interpreting model is
used only afterwards to identify the restriction idempotent with a set.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open FailureOfComposition.ProofSearch FailureOfComposition.UniformIndexQuotient
open FailureOfComposition.TypedNearProduct
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch

variable (T : ArithmeticTheory)

/-- Inverse-image membership is expressed by the given graph. -/
def graphPullCarrier {C D : Carrier} (f : GraphMorphism T C D) (E : Carrier) : Carrier :=
  let G := f.graph
  .mkSigma “x. ∃ y, !G.val x y ∧ !E.val y”

@[simp] theorem graphPullCarrier_eval {C D : Carrier} (f : GraphMorphism T C D) (E : Carrier)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x : M) :
    (graphPullCarrier T f E).val.Evalb ![x] ↔
      ∃ y : M, f.graph.val.Evalb ![x,y] ∧ E.val.Evalb ![y] := by
  simp [graphPullCarrier]

variable [𝗣𝗔 ⪯ T]

/-- This is source-category equality, with no standard-model premise or
model-disjointness premise. -/
theorem graphPullCarrier_idem {C D : Carrier} (f : GraphMorphism T C D) (E : Carrier) :
    Idem.pull (omegaArrow T f.programClass) (predicateIdem T E) =
      predicateIdem T (graphPullCarrier T f E) := by
  apply Idem.ext
  apply CodedHom.ext
  rw [Idem.pull_hom,restriction_val,comp_val]
  change domainClass T (predicateClass T E * f.programClass) =
    predicateClass T (graphPullCarrier T f E)
  apply programClass_ext T
  intro M _ _ x y
  simp only [domainClass_model,SyntacticModel.programRelation_mul,predicateClass_model,
    GraphMorphism.programClass_model,graphPullCarrier_eval]
  constructor
  · rintro ⟨rfl,_,w,hf,hE,_⟩
    exact ⟨⟨w,hf,hE⟩,rfl⟩
  · rintro ⟨⟨w,hf,hE⟩,rfl⟩
    exact ⟨rfl,w,w,hf,hE,rfl⟩

/-- The source predicate idempotent is interpreted as the partial identity on its truth
set at every element of every T-model. -/
theorem model_predicateIdem (C : Carrier) (M : Type)
    [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] :
    (SyntacticModel.modelRangeFunctor T M).mapIdem (predicateIdem T C) =
      setIdem {x : M | C.val.Evalb ![x]} := by
  apply Idem.ext
  apply PFun.ext
  intro x y
  change y ∈ (SyntacticModel.modelFunctor T M).map
    (omegaArrow T (predicateClass T C)) x ↔
      y ∈ partialIdentity (PartialFun.of M) {z : M | C.val.Evalb ![z]} x
  exact ((SyntacticModel.mem_model T M (omegaArrow T (predicateClass T C)) x y).trans
    ((SyntacticModel.mem_arrow T M (omegaArrow T (predicateClass T C)) _ _).trans
      (predicateClass_model T C M x y))).trans
    (mem_identity (X := PartialFun.of M) {z : M | C.val.Evalb ![z]} x y).symm

end CategoricalEssentialIncompleteness.V46.NamedArithmeticProofSearch
