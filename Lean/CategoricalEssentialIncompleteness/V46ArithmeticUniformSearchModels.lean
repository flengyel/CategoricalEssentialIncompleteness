/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticUniformSearch
public import CategoricalEssentialIncompleteness.V46ArithmeticSetModelLaws

/-! # Joint search in model coordinates and its single source diagonal

The search is selected for all fibers. Exact reversed values use disjointness
only at the displayed parameter, and the diagonal equation is the same source
equality for every parameter.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts PCategoryStruct
open FailureOfComposition FailureOfComposition.ProgramGraph FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedRecursionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
namespace CategoricalEssentialIncompleteness.V46.ArithmeticUniformSearch

/-- Numerical output before the final parity decoding. -/
def numberLift (C C' : Predicate₂) : nearProd (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔) ⟶
    omegaObject 𝗣𝗔 :=
  (PrintedObjectCoding.omegaProductIso 𝗣𝗔).hom ≫ numberSearch C C'

theorem lift_eq (C C' : Predicate₂) :
    lift C C' = numberLift C C' ≫ (omegaCoprodIso 𝗣𝗔).inv :=
  (Category.assoc _ _ _).symm

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local notation "F" => SyntacticModel.modelFunctor 𝗣𝗔 M

/-- The proved exponential product comparison in interpreted coordinates. -/
theorem mem_product_code (e x z : M) :
    z ∈ (F).map (PrintedObjectCoding.omegaProductIso 𝗣𝗔).hom (e,x) ↔
      z = ExponentialPairing.code e x := by
  rw [ArithmeticDiagonalCodes.mem_model_relation,
    PrintedObjectCoding.omegaProduct_value,PrintedObjectCoding.encodeProgram_model]
  change (∃ a b : M, pair e x = pair a b ∧ z = ExponentialPairing.code a b) ↔ _
  constructor
  · rintro ⟨a,b,he,hz⟩
    obtain ⟨rfl,rfl⟩ := (CodedObjectMembership.pair_eq_pair_iff e x a b).mp he
    exact hz
  · intro hz
    exact ⟨e,x,rfl,hz⟩

theorem mem_numberSearch (C C' : Predicate₂) (w z : M) :
    z ∈ (F).map (numberSearch C C') w ↔
      (eventualGraph (index C C')).val.Evalb ![w,z] := by
  rw [numberSearch,SyntacticModel.mem_model_index]
  rfl

theorem mem_numberLift (C C' : Predicate₂) (e x z : M) :
    z ∈ (F).map (numberLift C C') (e,x) ↔
      (eventualGraph (index C C')).val.Evalb ![ExponentialPairing.code e x,z] := by
  rw [numberLift,(F).map_comp,mem_comp]
  change (∃ w : M,
    w ∈ (F).map (PrintedObjectCoding.omegaProductIso 𝗣𝗔).hom (e,x) ∧
    z ∈ (F).map (numberSearch C C') w) ↔ _
  constructor
  · rintro ⟨w,hw,hz⟩
    have he := (mem_product_code M e x w).mp hw
    subst w
    exact (mem_numberSearch M C C' _ _).mp hz
  · intro hz
    exact ⟨ExponentialPairing.code e x,(mem_product_code M e x _).mpr rfl,
      (mem_numberSearch M C C' _ _).mpr hz⟩

/-- This chart does not assume the searched relation functional. -/
theorem mem_lift_graph (C C' : Predicate₂) (e x : M) (y : M ⊕ M) :
    y ∈ (F).map (lift C C') (e,x) ↔
      ∃ z : M,
        (eventualGraph (index C C')).val.Evalb ![ExponentialPairing.code e x,z] ∧
        y ∈ (F).map (omegaCoprodIso 𝗣𝗔).inv z := by
  rw [lift_eq,(F).map_comp,mem_comp]
  change (∃ z : M, z ∈ (F).map (numberLift C C') (e,x) ∧
    y ∈ (F).map (omegaCoprodIso 𝗣𝗔).inv z) ↔ _
  exact exists_congr fun z => and_congr (mem_numberLift M C C' e x z) Iff.rfl

/-- Even in an inconsistent fiber, every defined output has actual proof
or refutation evidence. The converse needs no fiber disjointness either. -/
theorem model_lift_domain (C C' : Predicate₂) (e x : M) :
    (∃ y : M ⊕ M, y ∈ (F).map (lift C C') (e,x)) ↔
      C.val.Evalb ![e,x] ∨ C'.val.Evalb ![e,x] := by
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨z,hz,_⟩ := (mem_lift_graph M C C' e x y).mp hy
    exact (search_domain_at C C' e x).mp ⟨z,hz⟩
  · intro h
    obtain ⟨z,hz⟩ := (search_domain_at C C' e x).mpr h
    have ht := (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).map_total
      (omegaCoprodIso 𝗣𝗔).inv (iso_total (omegaCoprodIso 𝗣𝗔).symm)
    obtain ⟨y,hy⟩ := ArithmeticSetModelLaws.total_has_value
      ((F).map (omegaCoprodIso 𝗣𝗔).inv) ht z
    exact ⟨y,(mem_lift_graph M C C' e x y).mpr ⟨z,hz,hy⟩⟩

/-- Positive evidence gives the reversed right value, at this fiber only. -/
theorem positive_lift_value (C C' : Predicate₂) (e : M)
    (hd : ∀ x : M, ¬(C.val.Evalb ![e,x] ∧ C'.val.Evalb ![e,x]))
    (x : M) (hx : C.val.Evalb ![e,x]) :
    Sum.inr x ∈ (F).map (lift C C') (e,x) := by
  apply (mem_lift_graph M C C' e x (Sum.inr x)).mpr
  refine ⟨2*x+1,(search_exact_at C C' e hd x _).mpr ?_,?_⟩
  · exact (reversedRelation_eval C C' e x _).mpr (Or.inl ⟨hx,rfl⟩)
  · exact (PartialSearchLift.mem_parity_decode_inr M _ _).mpr rfl

/-- Negative evidence gives the reversed left value, at this fiber only. -/
theorem negative_lift_value (C C' : Predicate₂) (e : M)
    (hd : ∀ x : M, ¬(C.val.Evalb ![e,x] ∧ C'.val.Evalb ![e,x]))
    (x : M) (hx : C'.val.Evalb ![e,x]) :
    Sum.inl x ∈ (F).map (lift C C') (e,x) := by
  apply (mem_lift_graph M C C' e x (Sum.inl x)).mpr
  refine ⟨2*x,(search_exact_at C C' e hd x _).mpr ?_,?_⟩
  · exact (reversedRelation_eval C C' e x _).mpr (Or.inr ⟨hx,rfl⟩)
  · exact (PartialSearchLift.mem_parity_decode_inl M _ _).mpr rfl

/-- The partial pairing retains the actual external parameter and uses
an actual output of the common source morphism as its second coordinate. -/
theorem mem_parameter_pairing (g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔)
    (e n : M) (hn : n ∈ (F).map g e) :
    (e,n) ∈ (F).map (partialPairing (𝟙 (omegaObject 𝗣𝗔)) g) e := by
  rw [partialPairing,(F).map_comp,mem_comp]
  refine ⟨(e,e),(ArithmeticDiagonalCodes.mem_source_diagonal M e (e,e)).mpr rfl,?_⟩
  rw [SyntacticModel.model_map_product,PFun.mem_prodMap,(F).map_id]
  exact ⟨Part.mem_some_iff.mpr rfl,hn⟩

/-- Interpret the one source equation. No pointwise source choice is
made when the displayed parameter changes. -/
theorem diagonal_model_output (C C' : Predicate₂) (e n : M)
    (hn : n ∈ (F).map (diagonal C C') e) (y : M ⊕ M)
    (hy : y ∈ (F).map (lift C C') (e,n)) :
    y ∈ (F).map ArithmeticDiagonalCodes.sourceParityDiagonal n := by
  have he : diagonal C C' ≫ ArithmeticDiagonalCodes.sourceParityDiagonal =
      partialPairing (𝟙 (omegaObject 𝗣𝗔)) (diagonal C C') ≫ lift C C' := by
    simpa only [ArithmeticDiagonalCodes.sourceParityDiagonal,Category.assoc]
      using diagonal_equation C C'
  have hr : y ∈ (F).map
      (partialPairing (𝟙 (omegaObject 𝗣𝗔)) (diagonal C C') ≫ lift C C') e := by
    rw [(F).map_comp,mem_comp]
    exact ⟨(e,n),mem_parameter_pairing M (diagonal C C') e n hn,hy⟩
  have hl : y ∈ (F).map (diagonal C C' ≫ ArithmeticDiagonalCodes.sourceParityDiagonal) e :=
    Eq.mpr (congrArg (fun f : omegaObject 𝗣𝗔 ⟶
      CategoryTheory.CoprodStruct.coprod (omegaObject 𝗣𝗔) (omegaObject 𝗣𝗔) =>
      y ∈ (F).map f e) he) hr
  rw [(F).map_comp,mem_comp] at hl
  obtain ⟨m,hm,hout⟩ := hl
  have hmn : m = n := Part.mem_unique hm hn
  exact hmn ▸ hout

/-- The reversed right value puts this common source output in D₁. -/
theorem positive_implies_beta (C C' : Predicate₂) (e : M)
    (hd : ∀ x : M, ¬(C.val.Evalb ![e,x] ∧ C'.val.Evalb ![e,x]))
    (n : M) (hn : n ∈ (F).map (diagonal C C') e)
    (hC : C.val.Evalb ![e,n]) : ArithmeticDiagonalCodes.beta.val.Evalb ![n] := by
  have hout := diagonal_model_output M C C' e n hn (Sum.inr n)
    (positive_lift_value M C C' e hd n hC)
  exact (ArithmeticDiagonalCodes.beta_eval n).mpr
    ⟨n,(ArithmeticDiagonalCodes.mem_sourceParityDiagonal_inr M n n).mp hout⟩

/-- The reversed left value puts the same source output in D₀. -/
theorem negative_implies_alpha (C C' : Predicate₂) (e : M)
    (hd : ∀ x : M, ¬(C.val.Evalb ![e,x] ∧ C'.val.Evalb ![e,x]))
    (n : M) (hn : n ∈ (F).map (diagonal C C') e)
    (hC' : C'.val.Evalb ![e,n]) : ArithmeticDiagonalCodes.alpha.val.Evalb ![n] := by
  have hout := diagonal_model_output M C C' e n hn (Sum.inl n)
    (negative_lift_value M C C' e hd n hC')
  exact (ArithmeticDiagonalCodes.alpha_eval n).mpr
    ⟨n,(ArithmeticDiagonalCodes.mem_sourceParityDiagonal_inl M n n).mp hout⟩

/-- Bounds may depend on the parameter. Disjointness is needed only in
that fiber, and the chosen source morphism is independent of every bound. -/
theorem avoids_at (C C' : Predicate₂) (e : M)
    (hd : ∀ x : M, ¬(C.val.Evalb ![e,x] ∧ C'.val.Evalb ![e,x]))
    (hAlpha : ∀ x : M, ArithmeticDiagonalCodes.alpha.val.Evalb ![x] → C.val.Evalb ![e,x])
    (hBeta : ∀ x : M, ArithmeticDiagonalCodes.beta.val.Evalb ![x] → C'.val.Evalb ![e,x])
    (n : M) (hn : n ∈ (F).map (diagonal C C') e) :
    ¬ C.val.Evalb ![e,n] ∧ ¬ C'.val.Evalb ![e,n] := by
  constructor
  · intro hC
    exact hd n ⟨hC,hBeta n (positive_implies_beta M C C' e hd n hn hC)⟩
  · intro hC'
    exact hd n ⟨hAlpha n (negative_implies_alpha M C C' e hd n hn hC'),hC'⟩

end Models
end CategoricalEssentialIncompleteness.V46.ArithmeticUniformSearch
