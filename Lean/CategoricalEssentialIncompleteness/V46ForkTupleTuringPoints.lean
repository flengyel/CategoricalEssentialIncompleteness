/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkTupleTuringComponents

/-! # The domain and output of the fork evaluator at tuple points -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open FailureOfComposition.Kleene (eval)
namespace CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation

open ForkDiagonalObstruction (tupleSpace)
open NumericalTuples (Point code)
open EnumerableCarriers (val)

def tupleProductCoding (X Y : TupleSpans) : NumericalTuples.comparison.obj (X.obj ⨯ Y.obj) ≅
    EnumerableCarriers.totalProduct (NumericalTuples.comparison.obj X.obj) (NumericalTuples.comparison.obj Y.obj) :=
  asIso (prodComparison NumericalTuples.comparison X.obj Y.obj) ≪≫ numericProduct _ _

def codedPairPoint {X Y : TupleSpans} (x : Point X.obj) (y : Point Y.obj) :
    {n // n ∈ (EnumerableCarriers.product (tupleCode.obj X) (tupleCode.obj Y)).support} :=
  ⟨Nat.pair (code _ x.val) (code _ y.val), by
    change (Nat.unpair _).1 ∈ NumericalTuples.codedSupport X.obj ∧
      (Nat.unpair _).2 ∈ NumericalTuples.codedSupport Y.obj
    simpa only [Nat.unpair_pair, NumericalTuples.code_mem_codedSupport] using And.intro x.property y.property⟩

def pairPoint {X Y : TupleSpans} (x : Point X.obj) (y : Point Y.obj) : Point (tupleProduct X Y).obj :=
  (NumericalTuples.pointEquiv _).symm
    (EnumerableCarriers.totalFunction (tupleProductCoding X Y).inv (codedPairPoint x y))

theorem pairPoint_value {X Y : TupleSpans} (x : Point X.obj) (y : Point Y.obj) :
    val (tupleProductIso X Y).inv (Nat.pair (code _ x.val) (code _ y.val)) =
      Part.some (code _ (pairPoint x y).val) := by
  apply Part.eq_some_iff.mpr
  rw [show code _ (pairPoint x y).val = _ from NumericalTuples.pointEquiv_symm_code _
    (EnumerableCarriers.totalFunction (tupleProductCoding X Y).inv (codedPairPoint x y))]
  exact EnumerableCarriers.totalFunction_mem (tupleProductCoding X Y).inv (codedPairPoint x y)

theorem binaryValue_graph {X Y Z : TupleSpans} (f : tupleProduct X Y ⟶ Z)
    (x : Point X.obj) (y : Point Y.obj) (z : Point Z.obj) :
    code _ z.val ∈ binaryValue f (code _ x.val) (code _ y.val) ↔ Graph f (pairPoint x y) z := by
  unfold binaryValue Graph
  rw [EnumerableCarriers.mem_val_comp, pairPoint_value]
  simp

theorem pairPoint_fst {X Y : TupleSpans} (x : Point X.obj) (y : Point Y.obj) :
    (prod.fst : X.obj ⨯ Y.obj ⟶ X.obj).toFun (pairPoint x y) = x := by
  apply (total_graph (X := tupleProduct X Y) (Y := X) prod.fst _ _).mp
  rw [← tuple_first]
  apply (binaryValue_graph _ _ _ _).mp
  unfold binaryValue
  change _ ∈ val ((tupleProductIso X Y).inv ≫ tupleCode.map
    (FullRestrictionProducts.first _ _ _ _ X Y)) _
  rw [FullRestrictionProducts.first_value, Iso.inv_hom_id_assoc]
  exact (EnumerableCarriers.mem_partialFst _ _ _ _).mpr
    ⟨(codedPairPoint x y).property, by simp only [Nat.unpair_pair]⟩

theorem pairPoint_snd {X Y : TupleSpans} (x : Point X.obj) (y : Point Y.obj) :
    (prod.snd : X.obj ⨯ Y.obj ⟶ Y.obj).toFun (pairPoint x y) = y := by
  apply (total_graph (X := tupleProduct X Y) (Y := Y) prod.snd _ _).mp
  rw [← tuple_second]
  apply (binaryValue_graph _ _ _ _).mp
  unfold binaryValue
  change _ ∈ val ((tupleProductIso X Y).inv ≫ tupleCode.map
    (FullRestrictionProducts.second _ _ _ _ X Y)) _
  rw [FullRestrictionProducts.second_value, Iso.inv_hom_id_assoc]
  exact (EnumerableCarriers.mem_partialSnd _ _ _ _).mpr
    ⟨(codedPairPoint x y).property, by simp only [Nat.unpair_pair]⟩

def point₂ (k x : ℕ) : Point (tupleSpace 2) := ⟨(k,x), Set.mem_univ _⟩
def point₄ (k z a b : ℕ) : Point (tupleSpace 4) := ⟨(k,z,a,b), Set.mem_univ _⟩

theorem endpoint_graph (k p l x a b : ℕ) :
    Graph endpointTau (pairPoint (point₂ k p) (point₂ l x)) (point₂ a b) ↔
      (a,b) ∈ Part.map Nat.unpair (eval p (Nat.pair l x)) := by
  rw [← binaryValue_graph]
  change Nat.pair a b ∈ binaryValue endpointTau (Nat.pair k p) (Nat.pair l x) ↔ _
  rw [endpointTau_value]
  constructor
  · intro h
    exact (Part.mem_map_iff _).mpr ⟨_, h, Nat.unpair_pair _ _⟩
  · rintro h
    obtain ⟨n, hn, he⟩ := (Part.mem_map_iff _).mp h
    have eq := congrArg Nat.pairEquiv he
    have en : n = Nat.pair a b := (Nat.pair_unpair n).symm.trans eq
    rwa [← en]

theorem left_graph (k p l x a b : ℕ) :
    Graph (evaluatedTau .left) (pairPoint (point₂ k p) (point₂ l x)) (point₂ a b) ↔
      (a,b) ∈ Part.map Nat.unpair (eval p (Nat.pair l x)) :=
  left_tau ▸ endpoint_graph k p l x a b

theorem right_graph (k p l x a b : ℕ) :
    Graph (evaluatedTau .right) (pairPoint (point₂ k p) (point₂ l x)) (point₂ a b) ↔
      (a,b) ∈ Part.map Nat.unpair (eval p (Nat.pair l x)) :=
  right_tau ▸ endpoint_graph k p l x a b

theorem center_tuple_graph (k p₀ p₁ p₂ l x₀ x₁ x₂ h y₀ y₁ y₂ : ℕ) :
    Graph (evaluatedTau .zero) (pairPoint (point₄ k p₀ p₁ p₂) (point₄ l x₀ x₁ x₂)) (point₄ h y₀ y₁ y₂) ↔
      EffectiveFork.quadCode (h,y₀,y₁,y₂) ∈ eval p₀ (EffectiveFork.quadCode (l,x₀,x₁,x₂)) ∧
      Nat.pair h y₁ ∈ eval p₁ (Nat.pair l x₁) ∧ Nat.pair h y₂ ∈ eval p₂ (Nat.pair l x₂) := by
  rw [← binaryValue_graph]
  exact center_graph _ _ _ _ _ _ _ _ _ _ _ _

end CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation
