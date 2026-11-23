/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkTupleTuring
public import CategoricalEssentialIncompleteness.V46ForkTupleEvaluationComparisons

/-! # The three components of the Turing morphism of Theorem B.7 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open FailureOfComposition.Kleene (eval)
namespace CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation

open ForkDiagonalObstruction (tupleSpace)
open EnumerableCarriers (val)

def evaluatedTau (j : WalkingSpan) :
    tupleProduct ((evaluation j).obj universal) ((evaluation j).obj universal) ⟶
      (evaluation j).obj universal :=
  (productComparison j universal universal).inv ≫ (evaluation j).map tau

private theorem evaluatedTau_code (j : WalkingSpan) :
    tupleCode.map (evaluatedTau j) =
      (tupleProductIso _ _).hom ≫ (componentProductIso j universal universal).inv ≫
        component j (forkCode.map tau) := by
  let i := productComparison j universal universal
  let c := componentProductIso j universal universal
  have h : tupleCode.map i.hom ≫ (tupleProductIso _ _).hom = c.hom :=
    component_product_comparison j universal universal
  apply (cancel_epi (tupleCode.map i.hom)).mp
  change tupleCode.map i.hom ≫ tupleCode.map (i.inv ≫ (evaluation j).map tau) = _
  rw [tupleCode.map_comp, ← tupleCode.map_comp_assoc, i.hom_inv_id, tupleCode.map_id, Category.id_comp,
    evaluation_value, ← Category.assoc, h, Iso.hom_inv_id_assoc]

theorem left_tau : evaluatedTau .left = endpointTau := by
  apply tupleCode.map_injective
  rw [evaluatedTau_code, tau_code, endpointTau_code]
  change _ ≫ (componentProductIso .left universal universal).inv ≫
    (componentProductIso .left universal universal).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]
  rfl

theorem right_tau : evaluatedTau .right = endpointTau := by
  apply tupleCode.map_injective
  rw [evaluatedTau_code, tau_code, endpointTau_code]
  change _ ≫ (componentProductIso .right universal universal).inv ≫
    (componentProductIso .right universal universal).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]
  rfl

theorem left_isTuring : @RecursionCategory.IsTuringMorphism TupleSpans _ tupleProducts.pcategoryStruct
    tupleProducts.pcategoryLaws endpoint endpoint endpoint (evaluatedTau .left) :=
  left_tau ▸ endpointTau_isTuring

theorem right_isTuring : @RecursionCategory.IsTuringMorphism TupleSpans _ tupleProducts.pcategoryStruct
    tupleProducts.pcategoryLaws endpoint endpoint endpoint (evaluatedTau .right) :=
  right_tau ▸ endpointTau_isTuring

def centerCode : tupleCode.obj (⟨tupleSpace 4⟩ : TupleSpans) ≅ EffectiveFork.natCarrier :=
  (PreservesRestriction.totalInclusion EnumerableCarriers.Carrier).mapIso (eqToIso codedCenterEq)

private theorem center_hom (n m : ℕ) : m ∈ val centerCode.hom n ↔ m = n := by
  have h : n ∈ (NumericalTuples.codedObject (tupleSpace 4)).obj.support := by
    rw [codedCenterEq]
    exact Set.mem_univ _
  exact (val_eqToHom codedCenterEq n m).trans (and_iff_right h)

private theorem center_inv (n m : ℕ) : m ∈ val centerCode.inv n ↔ m = n :=
  (val_eqToHom codedCenterEq.symm n m).trans (and_iff_right (Set.mem_univ n))

theorem center_value (p x : ℕ) : binaryValue (evaluatedTau .zero) p x =
    EffectiveFork.centerEval (Nat.pair p x) := by
  apply Part.ext
  intro n
  unfold binaryValue
  rw [evaluatedTau_code, tau_code, Iso.inv_hom_id_assoc]
  change n ∈ val ((componentProductIso .zero universal universal).inv ≫
      (componentProductIso .zero universal universal).hom ≫
      EnumerableCarriers.partialProdMap centerCode.hom centerCode.hom ≫
      EffectiveFork.centerEvaluator ≫ centerCode.inv) _ ↔ _
  rw [Iso.inv_hom_id_assoc]
  simp only [EnumerableCarriers.mem_val_comp, EnumerableCarriers.mem_partialProdMap_iff,
    center_hom, center_inv, Nat.unpair_pair]
  constructor
  · rintro ⟨m, ⟨hp, hx⟩, w, hw, rfl⟩
    have he : m = Nat.pair p x := (Nat.pair_unpair m).symm.trans (congrArg₂ Nat.pair hp hx)
    exact he ▸ hw
  · intro h
    exact ⟨Nat.pair p x, by simp only [Nat.unpair_pair, and_self], n, h, rfl⟩

/-- The central computation returns the proposed four-tuple exactly when both
endpoint computations return its projected pairs. -/
theorem center_graph (k p₀ p₁ p₂ l x₀ x₁ x₂ h y₀ y₁ y₂ : ℕ) :
    EffectiveFork.quadCode (h,y₀,y₁,y₂) ∈ binaryValue (evaluatedTau .zero)
        (EffectiveFork.quadCode (k,p₀,p₁,p₂)) (EffectiveFork.quadCode (l,x₀,x₁,x₂)) ↔
      EffectiveFork.quadCode (h,y₀,y₁,y₂) ∈ eval p₀ (EffectiveFork.quadCode (l,x₀,x₁,x₂)) ∧
      Nat.pair h y₁ ∈ eval p₁ (Nat.pair l x₁) ∧ Nat.pair h y₂ ∈ eval p₂ (Nat.pair l x₂) := by
  rw [center_value, EffectiveFork.mem_centerEval]
  simp only [EffectiveFork.centralEval, EffectiveFork.leftEval, EffectiveFork.rightEval,
    EffectiveFork.left_quad, EffectiveFork.right_quad, Nat.unpair_pair, Equiv.symm_apply_apply]

end CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation
